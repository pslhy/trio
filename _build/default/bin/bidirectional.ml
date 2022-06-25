open Specification
open Expr
open Vocab
open BidirectionalUtils
open Generator

(* (int list (points) * signature) -> vsa * depth *)
let learn_cache : (int list * signature, (vsa * int)) BatMap.t ref = ref BatMap.empty
let now_learning : (int list * signature) BatSet.t ref = ref BatSet.empty 

let trace_vsas : vsa list ref = ref []

module Candidate = 
struct
	type available_uncons = Expr.t BatSet.t

	type addr = int list 
	[@@deriving eq]
	type points = int list 
	[@@deriving eq]
	type subgoal = points * signature * Type.t 
	[@@deriving eq]
	type t = Expr.t * (addr * available_uncons * subgoal) list 

	let compare t1 t2 = 
		let (e1, subgoals_info1) = t1 in 
		let (e2, subgoals_info2) = t2 in 
		let e1_size = Expr.size_of_expr e1 in 
		let e2_size = Expr.size_of_expr e2 in 
		let e1_height = Expr.height_of_expr e1 in 
		let e2_height = Expr.height_of_expr e2 in 
		let e1_match_depth = Expr.match_depth e1 in 
		let e2_match_depth = Expr.match_depth e2 in 
		(* let e1_score = cost_of_expr_with_input e1 in 
		let e2_score = cost_of_expr_with_input e2 in  *)
		
		(* fewer holes 
			 shorter height
			 smaller size *)
		let n_subgoals1 = List.length subgoals_info1 in 
		let n_subgoals2 = List.length subgoals_info2 in 

		let e1_score = cost_of_expr e1 in 
		let e2_score = cost_of_expr e2 in 

		
		if e1_match_depth <> e2_match_depth then e1_match_depth - e2_match_depth
		else 
			if n_subgoals1 <> n_subgoals2 then n_subgoals1 - n_subgoals2 
			else 
				if e1_score <> e2_score then e1_score - e2_score
				(* if e1_score <> e2_score then ceil (e1_score -. e2_score) |> int_of_float *)
				else 
					if e1_size <> e1_size then e1_size - e2_size 
					else 
					if e1_height <> e2_height then e1_height - e2_height
					else  
						Stdlib.compare t1 t2 

end

module CandidateHeap = BatHeap.Make (Candidate) 

let rec plug candidate (addr, expr) =
	let rec plug_sub curr_addr e =
		match e with 
		| Wildcard ->  
			if addr = curr_addr then expr else e 
		| App (e1, e2) -> 
			App (plug_sub (curr_addr@[0]) e1, plug_sub (curr_addr@[1]) e2)
		| Func (p, e') -> Func (p, plug_sub (curr_addr@[1]) e')
		| Ctor (i, e') -> Ctor (i, plug_sub (curr_addr@[1]) e')
		| Unctor (i, e') -> Unctor (i, plug_sub (curr_addr@[1]) e')
		| Eq (b, e1, e2) -> 
			Eq (b, plug_sub (curr_addr@[1]) e1, plug_sub (curr_addr@[2]) e2)
		| Proj (i, e') -> Proj (i, plug_sub (curr_addr@[1]) e')
		| Fix (i, t, e') -> Fix (i, t, plug_sub (curr_addr@[2]) e')
		| Tuple es -> Tuple (BatList.mapi (fun i e' -> plug_sub (curr_addr@[i]) e') es)
		| Match (scrutinee, pats) -> 
			let pats' = 
				BatList.mapi (fun i (pattern, e') -> (pattern, plug_sub (curr_addr@[i+1]) e')) pats 
			in
			Match (scrutinee, pats') 
		| _ -> e
	in
	plug_sub [] candidate

	let init () = 
	let _ = learn_cache := BatMap.empty in
	let _ = now_learning := BatSet.empty in 
	()

let get_valid_recursive_components desired_ty ty_to_exprs available_uncons scrutinees = 
	(* let _ = my_prerr_endline (Printf.sprintf "scrutinees : %s" (string_of_set show scrutinees)) in
	let _ = my_prerr_endline (Printf.sprintf "available uncons : %s" (string_of_set show available_uncons)) in *)
	let exprs = try BatMap.find desired_ty ty_to_exprs with _ -> BatSet.empty in
	exprs 
	|> BatSet.filter (fun e -> is_recursive e)
	|> BatSet.filter (fun e -> using_allowed_unconstructor e available_uncons)
	|> BatSet.filter (fun e -> 
			let call_exprs = get_recursive_calls e in
			BatSet.for_all (function App (_, arg_exp) -> 
				(* let _ = my_prerr_endline (Printf.sprintf "arg_exp : %s" (Expr.show arg_exp)) in *)
				let es = 
					match arg_exp with 
					| Tuple es -> es
					| _ -> [arg_exp]
				in
				List.for_all (fun e -> 
					(not (BatSet.is_empty (get_unconstructors e))) || 
					(not (BatSet.mem e scrutinees))
				) es
			| _ -> assert false
			) call_exprs
		)

(* concolic eval recursive calls in the component
	e.g., 
		inputs : Cons(O(), Nil), Cons(O(), Cons(S(O()), Nil))
		component: Cons (O(), f (Un_Cons(x).1))  
		template: match x with Nil -> x | Cons _ -> _ 
		addr : [1] 
		plugged: match x with Nil -> x | Cons _ -> Cons (O(), f (Un_Cons(x).1)) 
		
		-> concolic eval f (Un_Cons(x).1) for each input
		obtains Un_Cons(x).1, Cons(O(), Cons (O(), Un_Cons(Un_Cons(x).1)))
		-> replace f (Un_Cons(x).1) in the component with them resp. 
		obtains Cons(O(), Un_Cons(x).1), Cons(O(), Cons(O(), Cons (O(), Un_Cons(Un_Cons(x).1))))
		-> evaluates 
		obtains Cons(O(), Nil), Cons(O(), Cons(O(), Cons (O(), Nil)))
		-> transform to exprs and match with desired outputs of the componentx
		*)
(* let check_violation_of_angelic_asssumption template addr component pts inputs = 
	let plugged = plug template (addr, component) in 
	let _ = my_prerr_endline (Printf.sprintf "plugged : %s" (Expr.show plugged)) in
	(* get all recursive calls in the component *)
	let rec_calls = get_recursive_calls component in 
	BatSet.fold (fun rec_call acc -> 
		concolic_eval spec max_int plugged (input : value)

	) component 

	let violate_angelic_assumption = 
		match rec_expr with 
		| App (Var i, arg_exp) when BatString.equal i target_func -> 
			let arg_vals = compute_signature spec inputs arg_exp in 
			let _ = my_prerr_endline (Printf.sprintf "arg_vals : %s" (string_of_signature arg_vals)) in
			let sg_pts = compute_signature spec (elems_of_indices pts arg_vals) plugged in 
			let _ = my_prerr_endline (Printf.sprintf "sig_pts : %s" (string_of_signature sg_pts)) in
			let _ = my_prerr_endline (Printf.sprintf "desired_sig_pts : %s" (string_of_signature desired_sig_pts)) in
			not (List.for_all2 (fun v1 v2 -> match_exprs (exp_of_value v1) (exp_of_value v2)) sg_pts desired_sig_pts)
		| _ -> false 
	in
	if violate_angelic_assumption then result  *)
		
let rec learn_funcs = [learn_ctor; learn_unctor; learn_tuple; learn_proj; learn_app; learn_match]
(* pts : indices of IO-examples which should be satisfied 
	 candidate : current sentential form, i.e., incomplete program 
	 addr : address of the hole to be filled *)
and learn candidate addr available_uncons pts spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	let sigs = 
		try 
			BatMap.find desired_type ty_to_sigs
			|> BatSet.filter (fun sg -> 
					(* let sg_pts = elems_of_indices pts sg in *)
					(* let desired_sig_pts_size = List.length desired_sig_pts in *)
					(* let sg_pts_size = List.length sg_pts in *)
					(* if desired_sig_pts_size = sg_pts_size then *)
						(* to support learn_proj, wildcard can be matched with anything *)
						(* List.for_all2 (fun v1 v2 -> (equal_value v1 v2) || (is_wildcard_value v1) || (is_wildcard_value v2)) desired_sig_pts sg_pts *)
					let expr = try BatMap.find sg sig_to_expr with _ -> assert false in
					(using_allowed_unconstructor expr available_uncons) &&
					(equal_signature (elems_of_indices pts sg) desired_sig_pts)
					(* else false *)
				)  
		with _ -> BatSet.empty 
	in
	let result = 
		(* there exists a (non-recursive) component immediately satisfying the spec *)
		if not (BatSet.is_empty sigs) then 
			(* if the candidate contains (or may contain in the future) recursive calls, must use all possible components 
				 any wildcard (hole) can be filled with a recursive call. so all candidates are targets *)
			if !Options.find_all then 	
				BatSet.fold (fun sg acc -> 
					let expr = try BatMap.find sg sig_to_expr with _ -> assert false in
					if (using_allowed_unconstructor expr available_uncons) then 
						let plugged = plug candidate (addr, expr) in 
						let _ = my_prerr_endline (Printf.sprintf "direct: plugging %s into %s and obtain %s" (Expr.show expr) (Expr.show candidate) (Expr.show plugged)) in 
						BatSet.add (plugged, []) acc
					else acc
				) sigs BatSet.empty 
			
				(* otherwise, choose the smallest component *)
			else
				let expr = 
					let init_expr = BatMap.find (BatSet.choose sigs) sig_to_expr in 
					(* init_expr *)
					BatSet.fold (fun sg min_expr -> 
						let expr = BatMap.find sg sig_to_expr in 
						(* if (Expr.size_of_expr expr) < (Expr.size_of_expr min_expr) then expr  *)
						if (Expr.cost_of_expr expr) < (Expr.cost_of_expr min_expr) then expr 	
						else min_expr
					) sigs init_expr
				in
				let plugged = plug candidate (addr, expr) in 
				let _ = my_prerr_endline (Printf.sprintf "direct: plugging %s into %s and obtain %s" (Expr.show expr) (Expr.show candidate) (Expr.show plugged)) in 
				BatSet.singleton (plugged, [])
		else BatSet.empty
	in
	if (not !Options.find_all) && (not (BatSet.is_empty result)) then result
	else
		(* add recursive components *)
		let result = 
			let scrutinees = get_scrutinees candidate in
			let rec_exprs = 
				get_valid_recursive_components desired_type ty_to_exprs available_uncons scrutinees
			in
			let inputs = List.map fst spec.spec in
			BatSet.fold (fun rec_expr acc ->
				let plugged = plug candidate (addr, rec_expr) in 
				(* let _ = my_prerr_endline (Printf.sprintf "plugged : %s" (Expr.show plugged)) in *)
				(* let violate_angelic_assumption = 
					match rec_expr with 
					| App (Var i, arg_exp) when BatString.equal i target_func -> 
						let arg_vals = compute_signature spec inputs arg_exp in 
						let _ = my_prerr_endline (Printf.sprintf "arg_vals : %s" (string_of_signature arg_vals)) in
						let sg_pts = compute_signature spec (elems_of_indices pts arg_vals) plugged in 
						let _ = my_prerr_endline (Printf.sprintf "sig_pts : %s" (string_of_signature sg_pts)) in
						let _ = my_prerr_endline (Printf.sprintf "desired_sig_pts : %s" (string_of_signature desired_sig_pts)) in
						not (List.for_all2 (fun v1 v2 -> match_exprs (exp_of_value v1) (exp_of_value v2)) sg_pts desired_sig_pts)
					| _ -> false 
				in
				if violate_angelic_assumption then result 
				else *)
					let _ = my_prerr_endline (Printf.sprintf "direct: plugging recursive %s into %s and obtain %s" (Expr.show rec_expr) (Expr.show candidate) (Expr.show plugged)) in 
					BatSet.add (plugged, []) acc
			) rec_exprs result
		in
		(* 다른 rule 들 사용한 결과 추가 *)
		let result = 
			List.fold_left (fun acc learn_func ->
				let result = 
					learn_func candidate addr available_uncons pts spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
				in
				(* let _ = 
				if not (BatSet.is_empty result) then 
					BatSet.iter (fun (next_candidate, hole_infos) -> 
						let _ = 
							my_prerr_endline (Printf.sprintf "learned next_candidate: %s" (Expr.show next_candidate))
						in
						let _ = 
							my_prerr_endline (Printf.sprintf "learned hole_infos: %s" 
								(string_of_list (fun (addr,_,(pts,_,_)) -> 
									Printf.sprintf "addr - %s, pts - %s"
									(string_of_list string_of_int addr)
									(string_of_list string_of_int pts)) hole_infos 
							)
							) 
						in 
						()
					) result 
				in *)
				BatSet.union result acc 
			) (*BatSet.empty*) result learn_funcs
		in 
		result 	  

and learn_ctor candidate addr available_uncons pts spec (desired_sig, _) _ = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_ctor: %s" (string_of_signature desired_sig_pts)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	(* 1. type check : desired output 이 모두 동일한 constructor 꼴인지 (C(v11,v12), .., C(vk1,vk2)) *)
	(* Constructor 때내고 각각 learn 한 후 vsa 구성 *)
	if (List.for_all (fun v -> is_ctor_value v) desired_sig_pts) then
		let constructors = 
			List.map (fun v -> match v with CtorV (i, _) -> i | _ -> assert false) desired_sig_pts
			|> list2set 
		in
		let is_of_all_same_constructors = (BatSet.cardinal constructors) = 1 in
		if is_of_all_same_constructors then
			let constructor = BatSet.choose constructors in 
			(* to prevent repeated generation of subproblems like  Un_Cons (Cons ...) *)
			let parent_expr = 
				if (BatList.is_empty addr) then Wildcard 
				else get_expr_from_addr candidate (BatList.remove_at ((List.length addr) - 1) addr) 
			in 
			(* let _ = my_prerr_endline (Printf.sprintf "parent: %s" (show parent_expr)) in *)
			let is_redundant_subproblem = 
				match parent_expr with 
				| Unctor (i, _) -> (BatString.equal i constructor)
				| _ -> false
			in
			if is_redundant_subproblem then BatSet.empty
			else
				let ekind = Ctor (constructor, Wildcard) in 
				let desired_sig' =  
					BatList.mapi (fun i v ->
						if (List.mem i pts) then 
							match v with 
							| CtorV(_, v') -> v'
							| _ -> assert false   
						else v 
					) desired_sig
				in
				let (desired_type',_) = try BatMap.find constructor spec.vc with _ -> assert false in  
				let plugged = plug candidate (addr, ekind) in 
				let addr' = addr @ [1] in 
				BatSet.singleton (plugged, [(addr', available_uncons, (pts, desired_sig', desired_type'))])
		else BatSet.empty
	else BatSet.empty

and learn_unctor candidate addr available_uncons pts spec (desired_sig, desired_type) _ = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_unctor: %s" (string_of_signature desired_sig_pts)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	let constructor_desired_types = 
		BatMap.foldi (fun ctor (arg_ty, parent_ty) acc ->
			let unctor_allowed =
				BatSet.exists (fun uncons_expr ->
					match uncons_expr with 
					| Unctor (i, _) -> BatString.equal i ctor
					| _ -> assert false  
				) available_uncons 
			in   
			(* to prevent repeated generation of subproblems like  Un_Cons (Cons ...) *)
			let parent_expr = 
				if (BatList.is_empty addr) then Wildcard 
				else get_expr_from_addr candidate (BatList.remove_at ((List.length addr) - 1) addr) 
			in 
			(* let _ = my_prerr_endline (Printf.sprintf "parent: %s" (show parent_expr)) in *)
			let is_redundant_subproblem = 
				match parent_expr with 
				| Ctor (i, _) -> (BatString.equal i ctor)
				| _ -> false
			in
			if (Type.equal arg_ty desired_type) && unctor_allowed && (not is_redundant_subproblem) then
				BatSet.add (ctor, parent_ty) acc 
			else acc 
		) spec.vc BatSet.empty 
	in 
	BatSet.fold (fun (ctor, desired_type') result ->
		let desired_sig' =
			BatList.mapi (fun i v ->
				if (List.mem i pts) then CtorV(ctor, v) else v 
			) desired_sig 
		in 
		let ekind = Unctor (ctor, Wildcard) in 
		let plugged = plug candidate (addr, ekind) in 
		let addr' = addr @ [1] in 
		(* peel off the outtermost unconstructor from each expr in available_uncons *)
		let available_uncons' = 
		  BatSet.fold (fun e acc -> 
				match e with 
				| Unctor (i, e') -> 
					if (BatString.equal i ctor) then 
						if is_unctor_exp e' then BatSet.add e' acc
						else acc 
					else BatSet.add e acc
				| _ -> acc
			) available_uncons BatSet.empty 
		in 
		BatSet.add (plugged, [(addr', available_uncons', (pts, desired_sig', desired_type'))]) result
	) constructor_desired_types BatSet.empty 
	
and learn_tuple candidate addr available_uncons pts spec (desired_sig, desired_type) 
	(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	(* desired output: TupleV(v11, v12), ... TupleV(vk1, vk2) *)
	(* -> Join(Tuple, learn v11, ..., vk1, learn v12, ..., k2) *)
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_tuple: %s" (string_of_signature desired_sig_pts)) in
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	(* type check : desired output 이 모두 tuple 꼴인지 *)
	if (List.for_all is_tuple_value desired_sig_pts) && (Type.is_tuple_type desired_type) then 
	(* type check : desired output 이 모두 같은 길이의 리스트의 tuple 꼴인지 *)
		let tuple_lens = 
			List.map (fun v -> 
				match v with 
				| TupleV vs -> List.length vs
				| _ -> assert false 
			) desired_sig_pts	|> list2set 
		in
		let _ = assert ((BatSet.cardinal tuple_lens) = 1) in 
		let tuple_len = BatSet.choose tuple_lens in
		(* unit value *)
		if tuple_len = 0 then 
			BatSet.empty
		else 
			let ekind = Tuple (BatList.make tuple_len Wildcard) in 
			let plugged = plug candidate (addr, ekind) in 
			let hole_infos = 
				List.fold_left (fun result i -> 
					let desired_sig' =  
						BatList.mapi (fun i' v ->
							if List.mem i' pts then 
								match v with 
								| TupleV vs -> List.nth vs i 
								| _ -> assert false
							else v (* doesn't care. just placeholder *)   
						) desired_sig
					in
					let desired_type' = List.nth (Type.destruct_tuple desired_type) i in 
					let addr' = addr @ [i] in 
					(addr', available_uncons, (pts, desired_sig', desired_type')) :: result
				) [] (BatList.range 0 `To (tuple_len - 1))	
			in 
			BatSet.singleton (plugged, hole_infos) 
	else BatSet.empty

and learn_proj candidate addr available_uncons pts spec (desired_sig, desired_type) 
	(ty_to_exprs, ty_to_sigs, sig_to_expr) =
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_proj: %s" (string_of_signature desired_sig_pts)) in
	(* desired output: v1, ..., vk 
	   desired type = T
		 desired_sig_pts : v_a, v_b *)
	(* there is a type ty = Tuple (..., T, ...) (T is i-th element of Tuple) 
	-> Proj (i, Tuple(..., ei, ...)) 
		 a,b-th elements of [[ei]] are v_a, v_b *)
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	(* BatMap.foldi (fun ty _ result -> 
		if not (Type.is_tuple_type ty) then result 
		else
			let tys = Type.destruct_tuple ty in 
			if not (List.mem desired_type tys) then result 
			else 
				let ind = BatOption.get (BatList.index_of desired_type tys) in
				let ekind = Proj (ind, Wildcard) in
				let plugged = plug candidate (addr, ekind) in
				let addr' = addr @ [1] in
				let desired_type' = ty in 
				let desired_sig' = 
					BatList.mapi (fun i v ->
						if List.mem i pts then 
							let desired_value = (List.nth desired_sig i) in 
							let tuplev = 
								BatList.mapi (fun i' _ -> if i' = ind then desired_value else WildcardV) tys
							in
							TupleV tuplev 
						else v
					) desired_sig 
				in
				BatSet.add (plugged, [(addr', available_uncons, (pts, desired_sig', desired_type'))]) result

	) ty_to_exprs BatSet.empty *)

	(* only non-recursive components are considered
		 because recursive components are not in sig_to_expr *)
	BatMap.foldi (fun sg expr result ->
		let sg_pts = (elems_of_indices pts sg) in
		(* only consider components whose outputs are tuples 
			 (e_1, e_2, ..., e_k).i is pointless   *)
		if not (List.for_all is_tuple_value sg_pts) || (is_tuple_exp expr) 
			|| not (using_allowed_unconstructor expr available_uncons) then result
		else 
			(* get length of tuples which are outputs of the currently considered component *)
			let tuple_len =
				let tuple_lens = 
					List.map (fun v -> 
						match v with 
						| TupleV vs -> List.length vs
						| _ -> assert false 
					) sg_pts |> list2set 
				in
				(* if outputs are tuples of varied length, something's wrong 
					because outputs should be of the same type *)
				let _ = assert ((BatSet.cardinal tuple_lens) = 1) in 
				BatSet.choose tuple_lens 
			in
			(* the output is unit. ignore this component *)
			if tuple_len = 0 then result 
			else 
				(* for i in 0 .. n-1, see if expr.i solves the subproblem. then each expr.i is a subsolution *)
				List.fold_left (fun result i ->
					let sg_pts_proj_i =
						List.map (fun v -> match v with TupleV vs -> List.nth vs i | _ -> assert false) sg_pts 
					in 
					(* if this component's output are tuples whose i'th elem is i'th elem of the desired sig,
						the component is the desired one. *)
					if (equal_signature sg_pts_proj_i desired_sig_pts) then
						let plugged = plug candidate (addr, Proj (i, expr)) in 
						BatSet.add (plugged, []) result
					else result  
				) result (BatList.range 0 `To (tuple_len - 1))  
	) sig_to_expr BatSet.empty  
	
and learn_match candidate addr available_uncons pts spec (desired_sig, desired_type) 
	(ty_to_exprs, ty_to_sigs, sig_to_expr) =
let desired_sig_pts = (elems_of_indices pts desired_sig) in
let parent_expr = 
	if (BatList.is_empty addr) then Wildcard 
	else get_expr_from_addr candidate (BatList.remove_at ((List.length addr) - 1) addr) 
in 
let _ = 
	my_prerr_endline (Printf.sprintf "learn_match : %s" (string_of_signature desired_sig_pts)) 
in
(* match is allowed only in the top-level or a branch *)
let is_match_allowed = 
	(List.length pts) > 1 && 
	(match parent_expr with 
	| Match _ -> true
	| Wildcard -> true
	| _ -> false)
in
if not is_match_allowed then BatSet.empty
else
(* 1. find scrutinees distinguishing wrt pts *)
(* {(scrutinee_1, [(pattern_1, pts_to_cover1), (pattern_2, pts_to_cover2), ...]) ...} *)
(* (Expr.t * (Pattern.t * int list)) set  *) 
let branching_infos =
	BatMap.foldi (fun ty sigs branching_infos ->
		match ty with 
		| Type.Named i ->
			let resolved_ty = try BatMap.find i spec.td with _ -> prerr_endline i; assert false in 
			if (Type.is_variant_type resolved_ty) then
				let n_variants = Type.destruct_variant resolved_ty |> List.length in
				BatSet.fold (fun sg branching_infos ->
					let scrutinee = try BatMap.find sg sig_to_expr with _ -> assert false in
					(* invalid scrutinee that uses unallowed unconstructors or of recursive call
						 어차피 ty_to_sigs 에는 recursive component 없음 *)
					if not (using_allowed_unconstructor scrutinee available_uncons) ||
						 (is_recursive scrutinee) then 
						branching_infos
					else  
						let sg_pts = elems_of_indices pts sg in
						let _ = assert (not (BatList.is_empty sg_pts)) in 
						(* (Pattern.t * int list) list *)
						let branches =
							(* Pattern.t -> int list *)
							let pat2pts =
								List.fold_left (fun m (desired_output, pt) ->
									match desired_output with 
									| CtorV (i, _) -> 
										let pat = Pattern.Ctor (i, Pattern.Wildcard) in
										let pts = try BatMap.find pat m with _ -> [] in  
										BatMap.add pat (pts @ [pt]) m 
									| _ -> m  
								) BatMap.empty (List.combine sg_pts pts) 
							in
							BatMap.foldi (fun pat pts branches ->
								branches @ [(pat, pts)]   
							) pat2pts []
						in
						(* sort branches : important! -- processing base cases first *)
						let branches =
							BatList.fast_sort (fun (pat1, _) (pat2, _) ->  Pattern.my_compare pat1 pat2 spec.vc) branches
						in 
						(* scrutinee should cover all constructors, i.e., branches *)
						if (List.length branches) = n_variants then
							BatSet.add (scrutinee, branches) branching_infos	  
						else branching_infos
				) sigs branching_infos 
			else branching_infos
		| _ -> branching_infos  
	) ty_to_sigs BatSet.empty  
in 
(* 2. 각 브랜치 별로 available_uncons 추가해서 learn *)		
(* branches: (Pattern.t * int list) list *)
BatSet.fold (fun (scrutinee, branches) result ->
	let _ = 
		my_prerr_endline (Printf.sprintf "scrutinee : %s" (Expr.show scrutinee)) 
	in
	let ekind = Match(scrutinee, List.map (fun (pat, _) -> (pat, Wildcard)) branches) in 
	let plugged = plug candidate (addr, ekind) in 
	let candidate_infos =
		BatList.mapi (fun ind (pat, pts) ->
			let _ = 
				my_prerr_endline (Printf.sprintf "pts : %s" (string_of_list string_of_int pts)) 
			in
			match pat with 
			| Pattern.Ctor (i, _) ->
				(* TODO : for base cases, ensure no recursive calls - 자동으로 그렇게 되는거 아닌가? (그 다음 learn 에서 component 로 solve)*)
				let available_uncons = BatSet.add (Unctor(i, scrutinee)) available_uncons in
				(* ind + 1 because 0 is reserved for scrutinee *)
				let addr' = addr @ [ind + 1] in 
				(addr', available_uncons, (pts, desired_sig, desired_type))
			| _ -> assert false
		) branches
	in
	BatSet.add (plugged, candidate_infos) result
) branching_infos BatSet.empty


(* learn app : user-defined function fuzzing *)
(* library: value -> (value (closure) * (value list)) list) *)
and learn_app candidate addr available_uncons pts spec (desired_sig, desired_type) 
		(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_app : (%s)-th of %s" (string_of_list string_of_int pts) (string_of_signature desired_sig)) in
	let _ = my_prerr_endline (Printf.sprintf "available uncons : %s" (string_of_set show available_uncons)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	(* recursive functions *)
	let inputs = List.map fst spec.spec in
	let input_ty = fst spec.synth_type in
	let outputs = List.map snd spec.spec in
	let output_ty = snd spec.synth_type in
	(* let _ = my_prerr_endline (Printf.sprintf "learn_app using components") in *)
	let arg_tys =
		match input_ty with
		| Type.Tuple ts -> ts
		| _ -> [input_ty]
	in
	let scrutinees = get_scrutinees candidate in
	(* let _ = my_prerr_endline (Printf.sprintf "scrutinees : %s" (string_of_set show scrutinees)) in *)
	(* conditions for termination guarnatee: 
			1) arguments should contain x, 
			2) no constructors 
			3) at least one unconstructor
			4) not a scrutinee of some match expr *)
	
	(* list of all possible arg expressions 
			(TODO: avoid combination explosion via generator) *)
	
	let rec_exprs = 
		get_valid_recursive_components output_ty ty_to_exprs available_uncons scrutinees
		|> BatSet.elements 
	in

	(* let rec_call_exprs = 
		let f_arg_exprs_list : Expr.t list list =
			List.map (fun arg_ty ->
				BatMap.find arg_ty ty_to_exprs
				|> BatSet.filter (contains_id target_func_arg)
				|> BatSet.filter (fun e -> (BatSet.is_empty (get_constructors e))) (* 필요? *)
				|> BatSet.filter (fun e -> using_allowed_unconstructor e available_uncons)
				|> BatSet.filter (fun e -> 
						(not (BatSet.is_empty (get_unconstructors e))) || 
						(match e with 
						| Tuple es -> 
							(* to avoid 
								match (x).0 with
								Cons(_) -> (f ((x).0, (x).0))
								Nil(_) -> _ 

								but the following is okay (because it involves an unconstructor)
								(match Un_Cons x . 1 with
									| Nil _ -> Some (Un_Cons x . 0)
									| Cons _ -> f (Un_Cons x . 1))

								*)
							not (List.exists (fun e -> BatSet.mem e scrutinees) es)
						| _ -> 
							not (BatSet.mem e scrutinees)
						)
					)
				|> BatSet.elements 
			) arg_tys
			|> BatList.n_cartesian_product
		in
		List.fold_left (fun result arg_exprs -> 
			let arg_expr = 
				if List.length arg_exprs = 1 then List.hd arg_exprs 
				else Tuple arg_exprs
			in
			let ekind = App(Var target_func, arg_expr) in 
			ekind :: result
		) [] f_arg_exprs_list 
	in *)


	let _= my_prerr_endline (Printf.sprintf "rec_exprs : %s" (string_of_list Expr.show rec_exprs)) in
	let result_rec = 
		if not (Type.equal output_ty desired_type) then BatSet.empty
		else
			(* there are some arguments violating the above conditions; skip *)
			if BatList.is_empty rec_exprs then 
				let _ = my_prerr_endline (Printf.sprintf "no components usable for arguments") in
				BatSet.empty
			else
				List.fold_left (fun result rec_expr -> 
					let plugged = plug candidate (addr, rec_expr) in 
					(* let _ = my_prerr_endline (Printf.sprintf "plugged : %s" (Expr.show plugged)) in
					let violate_angelic_assumption = 
						match rec_expr with 
						| App (Var i, arg_exp) when BatString.equal i target_func -> 
							let arg_vals = compute_signature spec inputs arg_exp in 
							let _ = my_prerr_endline (Printf.sprintf "arg_vals : %s" (string_of_signature arg_vals)) in
							let sg_pts = compute_signature spec (elems_of_indices pts arg_vals) plugged in 
							let _ = my_prerr_endline (Printf.sprintf "sig_pts : %s" (string_of_signature sg_pts)) in
							let _ = my_prerr_endline (Printf.sprintf "desired_sig_pts : %s" (string_of_signature desired_sig_pts)) in
							not (List.for_all2 (fun v1 v2 -> match_exprs (exp_of_value v1) (exp_of_value v2)) sg_pts desired_sig_pts)
						| _ -> false 
					in
					if violate_angelic_assumption then result 
					else *)
						BatSet.add (plugged, []) result
				) BatSet.empty rec_exprs 
	in
	let result_lib = 
		let top = BatList.make (List.length desired_sig) WildcardV in 
		(* BatSet.empty *)
		(* for each function expression component whose result type is desired_type, 
		   get all possible argument expressions (components + recursive calls)
			 filter out exprs which do not comply with the library
			 *)
		BatMap.foldi (fun fun_ty fun_sigs result -> 
			if not (Type.is_arrow_type fun_ty) then result
			else
				let (arg_ty, result_ty) = Specification.st_to_pair fun_ty in 
				if not (Type.equal result_ty desired_type) then result
				else
					let arg_tys = 
						let _ = assert (Type.equal result_ty desired_type) in 
						match arg_ty with
						| Type.Tuple ts -> ts
						| _ -> [arg_ty]
					in
					BatSet.fold (fun fun_sig result -> 
						(* recursive call *)
						if (equal_signature fun_sig top) then result
						else 
						let fun_expr = try BatMap.find fun_sig sig_to_expr with _ -> assert false in
						let arg_exprs_before_cartesian = 
							BatList.mapi (fun arg_index arg_ty ->
								let arg_sigs = try BatMap.find arg_ty ty_to_sigs with _ -> BatSet.empty in
								let arg_exprs = 
									BatSet.fold (fun arg_sig arg_exprs -> 
										let arg_expr = try BatMap.find arg_sig sig_to_expr with _ -> assert false in
										let okay = 
											(* (not (is_app_exp arg_expr)) && *)
											(using_allowed_unconstructor arg_expr available_uncons) &&
											List.for_all (fun pt -> 
												let desired_output = List.nth desired_sig pt in 
												let arg_output = List.nth arg_sig pt in
												let funcv = (List.nth fun_sig pt) in 
												if (BatMap.mem desired_output !Tracelearner.library) then 
													(* library: value -> (closure * fun_type * (arg value list)) list) *)
													let funv_ty_argvs = BatMap.find desired_output !Tracelearner.library in 
													List.exists (fun (funcv', fun_ty', argvs) ->  
														(Type.equal fun_ty' fun_ty) && (Expr.equal_value funcv' funcv) &&
														(Expr.equal_value (List.nth argvs arg_index) arg_output)
													) funv_ty_argvs
												else false 
											) pts 
										in
										if okay then 
											arg_expr :: arg_exprs 
										else arg_exprs 
									) arg_sigs []
								in 
								if (Type.equal output_ty arg_ty) then
									arg_exprs @ rec_exprs
								else arg_exprs
							) arg_tys
						in 
						let arg_exprs_list = BatList.n_cartesian_product arg_exprs_before_cartesian in 
						List.fold_left (fun result arg_exprs -> 
							let isrec, ekind = 
								List.fold_left (fun (is_rec, expr) arg_expr -> 
									let is_rec = is_rec || (is_recursive arg_expr) in
									(is_rec, App(expr, arg_expr))
								) (false, fun_expr) arg_exprs 
							in 
							if isrec || 
							  (let sg = compute_signature spec inputs ekind in 
								 equal_signature (elems_of_indices pts sg) desired_sig_pts) then 
								let plugged = plug candidate (addr, ekind) in 
								BatSet.add (plugged, []) result
							else result 
						) result arg_exprs_list
					) fun_sigs result 
		) ty_to_sigs BatSet.empty  
	in
	BatSet.union result_rec result_lib


(* 

		(* desired_fun_argvs : for each desired output o_i, triple of (f, fun_ty, v1...vk) s.t. (..(f v1)..vk)..) = o_i *)		
		let desired_fun_argvs_lst = 
			BatList.mapi (fun i output -> 
				if (BatList.mem i pts) && (BatMap.mem output !Tracelearner.library) then 
					BatMap.find output !Tracelearner.library
				else 
					(* dummy for cartesian product computation *)
					[(WildcardV, Type._unit, [WildcardV])]
			) desired_sig
			|> BatList.n_cartesian_product
		in 
		List.fold_left (fun result desired_fun_argvs -> 
			let _ = assert ((List.length desired_fun_argvs) = List.length desired_sig) in
			(* desired_fun_argvs : for each desired output o_i, triple of (f, fun_ty, v1...vk) s.t. (..(f v1)..vk)..) = o_i *)
			let funcv_tys = 
				List.fold_left (fun acc (funcv,fun_ty,_) -> 
					if is_wildcard_value funcv then acc else BatSet.add (funcv,fun_ty) acc
				) BatSet.empty desired_fun_argvs
			in
			let is_single_funv = (BatSet.cardinal funcv_tys) = 1 in 
			if not is_single_funv then result
			else 
				let funcv, fun_ty = BatSet.choose funcv_tys in 
				let funcv_sig = BatList.make (BatList.length desired_sig) funcv in 
				let _ = assert (BatMap.mem funcv_sig sig_to_expr) in 
				let fun_expr = BatMap.find funcv_sig sig_to_expr in
				let (arg_ty, result_ty) = Specification.st_to_pair fun_ty in 
				let arg_tys = 
					let _ = assert (Type.equal result_ty desired_type) in 
					match arg_ty with
					| Type.Tuple ts -> ts
					| _ -> [arg_ty]
				in
				(* type subgoal = points * signature * Type.t  *)
				(* type t = Expr.t * (addr * available_uncons * subgoal) list  *)
				let plugged = 
					let ekind = List.fold_left (fun acc _ -> App(acc, Wildcard)) Wildcard arg_tys in 
					plug candidate (addr, ekind) 
				in 
				let addrs = 
					List.fold_left (fun acc _ ->  
						(* App(App(App(f,a1),a2),a3)  
						[0;0;0] [0;0;1] [0;1] [1] *)
						(List.map (fun lst -> 0::lst) acc) @ [[1]]
					) [ addr@[0] ; addr@[1] ] (List.tl arg_tys) in
				let _,hole_infos = 
					let funcv_hole_info = 
						(List.hd addrs, available_uncons, (pts, BatList.make (List.length desired_sig) funcv, fun_ty))
					in
					List.fold_left (fun (arg_index, hole_infos) arg_addr -> 
						let desired_sig' = 
							List.fold_left (fun acc (funcv,_,args) -> 
								if is_wildcard_value funcv then acc @ [WildcardV] 
								else 
									let _ = assert ((List.length args) > arg_index) in 
									acc @ [List.nth args arg_index]
							) [] desired_fun_argvs 
						in 
						let desired_type' = List.nth arg_tys arg_index in 
						let hole_info = (arg_addr, available_uncons, (pts, desired_sig', desired_type')) in
						(arg_index + 1, hole_infos @ [hole_info])
					) (0, [funcv_hole_info]) (List.tl addrs)
				in 
				BatSet.add (plugged, hole_infos) result  
		) BatSet.empty desired_fun_argvs_lst 
	in  *)

(* 
	let result_rec = 
		(* spec: [Nil] -> 0,  [Cons(0,Nil)] -> 1, [Cons(0,Cons(0,Nil))] -> 2 *)
		(* if desired_sig_pts = [_, 0, 1] *)
		(*   f (learn [_, Nil, Cons(0,Nil)] [1,2]) *)
		(*   f (learn [|spec.spec|] x |f arg_len| ) *)
		(* if desired_sig_pts not in o1, o2 *)
		(*   f (comp1, comp2), f (comp1', comp2') ... all products of components *)
		let in_spec = List.for_all (fun v -> List.mem v outputs) desired_sig_pts in
		if not (Type.equal output_ty desired_type) then BatSet.empty
		else
			let result_rec = 
				(* if in_spec then
					let _ = my_prerr_endline (Printf.sprintf "learn_app from I/O example") in
					let desired_sig' =
						List.map (fun (desired_output, i) ->
							if not (List.mem i pts) then WildcardV
							else
								try BatList.assoc_inv desired_output spec.spec with _ -> assert false
						) (List.combine desired_sig (BatList.range 0 `To ((List.length desired_sig) - 1)))
					in
					let ekind = App(Var target_func, Wildcard) in 
					let plugged = plug candidate (addr, ekind) in 
					let addr' = addr @ [1] in 
					BatSet.singleton (plugged, [(addr', available_uncons, (pts, desired_sig', input_ty))])
				else  *)
					BatSet.empty 
			in
			let _ = my_prerr_endline (Printf.sprintf "learn_app using components") in
			let arg_tys =
				match input_ty with
				| Type.Tuple ts -> ts
				| _ -> [input_ty]
			in
			let scrutinees = get_scrutinees candidate in
			(* let _ = my_prerr_endline (Printf.sprintf "scrutinees : %s" (string_of_set show scrutinees)) in *)
			(* conditions for termination guarnatee: 
					1) arguments should contain x, 
					2) no constructors 
					3) at least one unconstructor
					4) not a scrutinee of some match expr *)
			
			(* list of all possible arg expressions 
					(TODO: avoid combination explosion via generator) *)
			
			let arg_exprs_list : Expr.t list list =
				List.map (fun arg_ty ->
					BatMap.find arg_ty ty_to_exprs
					|> BatSet.filter (contains_id target_func_arg)
					|> BatSet.filter (fun e -> (BatSet.is_empty (get_constructors e)))
					|> BatSet.filter (fun e -> using_allowed_unconstructor e available_uncons)
					|> BatSet.filter (fun e -> 
							(not (BatSet.is_empty (get_unconstructors e))) || 
						  (match e with 
							| Tuple es -> 
								(* to avoid 
								  match (x).0 with
									Cons(_) -> (f ((x).0, (x).0))
									Nil(_) -> _ 

									but the following is okay (because it involves an unconstructor)
									(match Un_Cons x . 1 with
										| Nil _ -> Some (Un_Cons x . 0)
										| Cons _ -> f (Un_Cons x . 1))

									*)
								not (List.exists (fun e -> BatSet.mem e scrutinees) es)
							| _ -> 
								not (BatSet.mem e scrutinees)
							)
						)
					|> BatSet.elements 
				) arg_tys
				|> BatList.n_cartesian_product
			in
			(* there are some arguments violating the above conditions; skip *)
			if BatList.is_empty arg_exprs_list then 
				let _ = my_prerr_endline (Printf.sprintf "no components usable for arguments") in
				BatSet.empty
			else
				try 
					List.fold_left (fun result arg_exprs -> 
						let arg_expr = 
							if List.length arg_exprs = 1 then List.hd arg_exprs 
							else Tuple arg_exprs
						in
						let ekind = App(Var target_func, arg_expr) in 
						let plugged = plug candidate (addr, ekind) in 
						(* from spec : TODO check if it works well *)
						let _ = 
							if in_spec then 
								let sg = compute_signature spec inputs arg_expr in 
								let is_arg_expr_from_spec = 
									BatList.for_all (fun pt ->
										if List.mem pt pts then 
											let component_output = List.nth sg pt in
											let desired_output = List.nth desired_sig pt in
											match BatList.index_of (component_output, desired_output) spec.spec with 
											| None -> false 
											| Some i -> i <> pt
										else true 
									) pts 
								in
								if is_arg_expr_from_spec then raise (SubSolutionFound plugged)
						in
						
						(* let _ = 
							my_prerr_endline (Printf.sprintf "through concolic eval, checking feasibility of %s" (Expr.show plugged)) 
						in
						let feasible = 
							let filter_fun = if !Options.trace_complete then BatList.for_all else BatList.exists in 
							filter_fun (fun pt -> 
								let trace_vsa = (List.nth !trace_vsas pt) in
								let input = List.nth inputs pt in 
								let upper_bound = 
									let max_trace_size = 
										snd (pgm_size_of_vsa trace_vsa)
										(* BatList.max (List.map (fun vsa -> snd (pgm_size_of_vsa trace_vsa)) !trace_vsas)  *)
									in
									max_trace_size
								in 
								try
									let trace_expr = concolic_eval spec upper_bound plugged input in 
									let _ = 
										my_prerr_endline (Printf.sprintf "trace expr: %s" (Expr.show trace_expr)) 
									in
									let matched = match_expr_vsa trace_expr trace_vsa in
									let _ = 
										my_prerr_endline (Printf.sprintf "matched? %s" (if matched then "yes" else "no"))
									in
									matched
								with exn -> 
									let _ = my_prerr_endline (Printf.sprintf "exception: %s" (Printexc.to_string exn)) in
									false 
							) pts 
						in 
						if feasible then  *)
							BatSet.add (plugged, []) result 
						(* else result  *)
					) result_rec arg_exprs_list 
				with SubSolutionFound plugged -> BatSet.singleton (plugged, [])
	in
	(* non recursive functions *)
	let result_lib = 
		(* BatSet.empty *)
		(* library: value -> (closure * fun_type * (arg value list)) list) 
			 desired_sig: [o1, o2, o3, o4] 
			 pts: [1, 3]
			 desired_sig_fun :  [func_v1, o2, func_v1, o4], [func_v2, o2, func_v2, o4] ... 
			 desired_sig_arg1 : [arg_v1, o2, arg_v1', o4],  [arg_v1'', o2, arg_v1''', o4] ... 
			 desired_sig_arg2 : [arg_v2, o2, arg_v2', o4],  [arg_v2'', o2, arg_v2''', o4] ... 
			 ...
			 desired_sig_argn : [arg_vn, o2, arg_vn', o4],  [arg_vn'', o2, arg_vn''', o4]

			  *)
		
		(* desired_fun_argvs : for each desired output o_i, triple of (f, fun_ty, v1...vk) s.t. (..(f v1)..vk)..) = o_i *)		
		let desired_fun_argvs_lst = 
			BatList.mapi (fun i output -> 
				if (BatList.mem i pts) && (BatMap.mem output !Tracelearner.library) then 
					BatMap.find output !Tracelearner.library
				else 
					(* dummy for cartesian product computation *)
					[(WildcardV, Type._unit, [WildcardV])]
			) desired_sig
			|> BatList.n_cartesian_product
		in 
		List.fold_left (fun result desired_fun_argvs -> 
			let _ = assert ((List.length desired_fun_argvs) = List.length desired_sig) in
			(* desired_fun_argvs : for each desired output o_i, triple of (f, fun_ty, v1...vk) s.t. (..(f v1)..vk)..) = o_i *)
			let funcv_tys = 
				List.fold_left (fun acc (funcv,fun_ty,_) -> 
					if is_wildcard_value funcv then acc else BatSet.add (funcv,fun_ty) acc
				) BatSet.empty desired_fun_argvs
			in
			let is_single_funv = (BatSet.cardinal funcv_tys) = 1 in 
			if not is_single_funv then result
			else 
				let funcv, fun_ty = BatSet.choose funcv_tys in 
				let (arg_ty, result_ty) = Specification.st_to_pair fun_ty in 
				let arg_tys = 
					let _ = assert (Type.equal result_ty desired_type) in 
					match arg_ty with
					| Type.Tuple ts -> ts
					| _ -> [arg_ty]
				in
				(* let _ = 
					List.iter (fun (funcv,fun_ty,argvs) -> 
						prerr_endline ("funcv : " ^ (Expr.show_value funcv));
						prerr_endline ("fun_ty : " ^ (Type.show fun_ty));
						prerr_endline ("argvs : " ^ (string_of_list Expr.show_value argvs));
						assert ((List.length argvs) = (List.length arg_tys) || (is_wildcard_value funcv))
					) desired_fun_argvs 
				in  *)
				(* type subgoal = points * signature * Type.t  *)
				(* type t = Expr.t * (addr * available_uncons * subgoal) list  *)
				let plugged = 
					let ekind = List.fold_left (fun acc _ -> App(acc, Wildcard)) Wildcard arg_tys in 
					plug candidate (addr, ekind) 
				in 
				let addrs = 
					List.fold_left (fun acc _ ->  
						(* App(App(App(f,a1),a2),a3)  
						[0;0;0] [0;0;1] [0;1] [1] *)
						(List.map (fun lst -> 0::lst) acc) @ [[1]]
					) [ addr@[0] ; addr@[1] ] (List.tl arg_tys) in
				let _,hole_infos = 
					let funcv_hole_info = 
						(List.hd addrs, available_uncons, (pts, BatList.make (List.length desired_sig) funcv, fun_ty))
					in
					List.fold_left (fun (arg_index, hole_infos) arg_addr -> 
						let desired_sig' = 
							List.fold_left (fun acc (funcv,_,args) -> 
								if is_wildcard_value funcv then acc @ [WildcardV] 
								else 
									let _ = assert ((List.length args) > arg_index) in 
									acc @ [List.nth args arg_index]
							) [] desired_fun_argvs 
						in 
						let desired_type' = List.nth arg_tys arg_index in 
						let hole_info = (arg_addr, available_uncons, (pts, desired_sig', desired_type')) in
						(arg_index + 1, hole_infos @ [hole_info])
					) (0, [funcv_hole_info]) (List.tl addrs)
				in 
				BatSet.add (plugged, hole_infos) result  
		) BatSet.empty desired_fun_argvs_lst 
		

		(* List.map (fun pt ->
			let output = List.nth desired_sig pt in
			if not (BatMap.mem output !Tracelearner.library) then Empty
			else
				let funcv_args_list = BatMap.find output !Tracelearner.library in
				let vsas = 
  				List.fold_left (fun vsas (funcv, fun_ty, args) ->
  					try
  						(* only funcv matters (wildcards are just placeholders) *)
    					let desired_sig' =
  							BatList.mapi (fun i v -> if i = pt then funcv else v) 
  								(BatList.make (List.length desired_sig) WildcardV)
    					in
    					let fun_vsa =
    						(* available_depth = 1 since we are only interested in components *)
    						learn 1 available_uncons [pt] spec (desired_sig', fun_ty)
    							(ty_to_exprs, ty_to_sigs, sig_to_expr)
    					in
  						let _ = my_prerr_endline (Printf.sprintf "fun_vsa: %s" (string_of_vsa fun_vsa)) in
    					let _ = if fun_vsa = Empty then raise LearnFailure in
    					let vsa =
  							let arg_tys =
  								let arg_ty, result_ty = Specification.st_to_pair fun_ty in
  								let _ = assert (Type.equal result_ty desired_type) in
  								match arg_ty with
  								| Type.Tuple ts -> ts
  								| _ -> [arg_ty]
  							in
  							let _ = assert ((List.length args) = (List.length arg_tys)) in
      					List.fold_left (fun vsa (arg, arg_ty) ->
      						let desired_sig' =
  									BatList.mapi (fun i v -> if i = pt then arg else v) 
  										(BatList.make (List.length desired_sig) WildcardV)
        						(* arg :: (BatList.make ((List.length desired_sig) - 1) WildcardV) *)
        					in
      						let vsa_for_arg =
      							learn (available_depth - 1) available_uncons [pt] spec (desired_sig', arg_ty)
      								(ty_to_exprs, ty_to_sigs, sig_to_expr)
      						in
    							if vsa_for_arg = Empty then raise LearnFailure
    							else Join (App (Wildcard, Wildcard), [vsa; vsa_for_arg])
      					) fun_vsa (List.combine args arg_tys)
    					in
  						let _ = my_prerr_endline (Printf.sprintf "total_vsa: %s" (string_of_vsa vsa)) in
    					BatSet.add vsa vsas
  					with LearnFailure -> vsas
  				) BatSet.empty funcv_args_list
				in
				if (BatSet.is_empty vsas) then Empty 
				else Union vsas
		) pts *)
	in
	(* let vsa_lib = intersect_vsa_list vsas_lib in *)
	BatSet.union result_rec result_lib *)

let update_heap available_depth candidate_info heap spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	let next_candidate_infos = 
		let (next_candidate, hole_infos) = candidate_info in 
		if (BatList.is_empty hole_infos) then 
			BatSet.empty 
		else 
			let (addr, available_uncons, (pts, desired_sig, desired_type)) = List.hd hole_infos in 
			let hole_infos' = List.tl hole_infos in 
			let expanded_result = 
				(* already consumed the available depth *)
				if (List.length addr) > available_depth then BatSet.empty 
				else 
					learn next_candidate addr available_uncons pts spec 
								(desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
			in
			BatSet.fold (fun (next_candidate, hole_infos) next_candidate_infos -> 
				(* let _ = 
					my_prerr_endline (Printf.sprintf "added next_candidate: %s" (Expr.show next_candidate))
				in
				let _ = 
					my_prerr_endline (Printf.sprintf "added hole_infos: %s" 
						(string_of_list (fun (addr,_,(pts,_,_)) -> 
							Printf.sprintf "addr - %s, pts - %s"
							(string_of_list string_of_int addr)
							(string_of_list string_of_int pts)) hole_infos 
					)
					) 
				in *)
				let new_hole_infos = hole_infos @ hole_infos' in 
				let can_be_added = 
					(* if not recursive or no holes to be filled, no need to do symbolic execution 
						 *)
					if !Options.no_filter || (not (is_recursive next_candidate)) || (BatList.is_empty new_hole_infos) then true
					else 
						let inputs = List.map fst spec.spec in
						let _ = 
							my_prerr_endline (Printf.sprintf "through concolic eval, checking feasibility of %s" (Expr.show next_candidate)) 
						in
						let feasible =
							let filter_fun = if true (*!Options.trace_complete*) then BatList.for_all else BatList.exists in 
							filter_fun
							 (fun pt -> 
								(* let _ = my_prerr_endline (Printf.sprintf "input [%d]" pt) in *)
								let trace_vsa = (List.nth !trace_vsas pt) in
								let input = List.nth inputs pt in 
								let upper_bound = 
									let max_trace_size = 
										snd (pgm_size_of_vsa trace_vsa)
										(* BatList.max (List.map (fun vsa -> snd (pgm_size_of_vsa trace_vsa)) !trace_vsas)  *)
									in
									max_trace_size
								in 
								try
									let trace_expr = 
										(* let next_candidate = replace_holes spec.ec next_candidate in *)
										concolic_eval spec upper_bound next_candidate input 
									in 
									let _ = 
										my_prerr_endline (Printf.sprintf "trace expr: %s" (Expr.show trace_expr)) 
									in
									let matched = match_expr_vsa trace_expr trace_vsa in
									let _ = 
										my_prerr_endline (Printf.sprintf "matched? %s" (if matched then "yes" else "no"))
									in
									matched
								with exn -> 
									let _ = my_prerr_endline (Printf.sprintf "exception: %s" (Printexc.to_string exn)) in
									false 
							) pts 
						in 
						feasible
				in
				if can_be_added then 
					let new_hole_infos = BatList.fast_sort (fun (addr1,_,_) (addr2,_,_) -> Stdlib.compare addr1 addr2) new_hole_infos in 
					let _ = my_prerr_endline (Printf.sprintf "added to the queue: %s" (Expr.show next_candidate)) in
					BatSet.add (next_candidate, new_hole_infos) next_candidate_infos 
				else next_candidate_infos
			) expanded_result BatSet.empty 
	in 
	(* check each new candidate's feasibility (only when it involves recursions) *)
	(* let next_candidate_infos = BatSet.filter ... in *)
	BatSet.fold CandidateHeap.add next_candidate_infos heap 
	

let main_loop spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let input_values = List.map fst spec.spec in
	let pts = (BatList.range 0 `To ((List.length input_values) - 1)) in
	let initial_candidate_info = (Wildcard, [[], BatSet.empty, (pts, desired_sig, desired_type)]) in 
	let heap = CandidateHeap.add initial_candidate_info CandidateHeap.empty in 
	let rec iter heap = 
		if (CandidateHeap.size heap) = 0 then raise NoSolInVSA 
		else 
			let next_candidate_info = CandidateHeap.find_min heap in 
			let (next_candidate, hole_infos) = next_candidate_info in 
			let _ = my_prerr_endline (Printf.sprintf "heap size: %d" (CandidateHeap.size heap)) in
			let _ = my_prerr_endline (Printf.sprintf "chosen candidate: %s" (Expr.show next_candidate)) in
			let _ = 
				my_prerr_endline (Printf.sprintf "hole_infos: %s" 
					(string_of_list (fun (addr,_,(pts,_,_)) -> 
						Printf.sprintf "addr - %s, pts - %s"
						(string_of_list string_of_int addr)
						(string_of_list string_of_int pts)) hole_infos 
				)
				) 
			in
			let solution_opt = 
				(* complete program *)
				if (BatList.is_empty hole_infos) then 
					let sg = compute_signature spec input_values next_candidate in
					let _ = my_prerr_endline (Printf.sprintf "  desired signature: %s" (string_of_list Expr.show_value desired_sig)) in
					let _ = my_prerr_endline (Printf.sprintf "component signature: %s" (string_of_list Expr.show_value sg)) in
					(* solution found! *)
					if (equal_signature sg desired_sig) && (not !Options.always_recursive || (is_recursive next_candidate)) then Some next_candidate
					(* not a solution; ignore *)
					else None
				(* incomplete program *)
				else None
			in
			match solution_opt with 
			| Some sol -> sol 
			| None -> 
				let next_heap = 
					update_heap !Options.max_height next_candidate_info (CandidateHeap.del_min heap) 
						spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
				in
				iter next_heap
	in
	iter heap 


(** Main DUET algorithm *)						
let synthesis spec =
	let input_values = List.map fst spec.spec in
	let desired_sig = List.map snd spec.spec in
	let desired_ty = snd spec.synth_type in 
	let ty_to_exprs = BatMap.empty in
	let ty_to_sigs = BatMap.empty in 
	let sig_to_expr = BatMap.empty in
	(* collect exprs that can be used as a variable in a match expression 
			results are without recursive components *)
	let (ty_to_exprs', ty_to_sigs', sig_to_expr') = 
		let rec fix depth (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
			let (ty_to_exprs', ty_to_sigs', sig_to_expr') = 
				get_components_of_depth ~grow_funcs:[grow_unctor; grow_proj] spec (BatMap.empty, BatMap.empty, BatMap.empty) (depth, depth + 1)
			in
			if (BatMap.compare BatSet.compare ty_to_exprs' ty_to_exprs) = 0 then 
				(ty_to_exprs, ty_to_sigs, sig_to_expr)
			else fix (depth + 1) (ty_to_exprs', ty_to_sigs', sig_to_expr')
		in
		fix 1 (ty_to_exprs, ty_to_sigs, sig_to_expr)
	in
	let rec iter depth (ty_to_exprs, ty_to_sigs, sig_to_expr) =
		let vsas =
			let (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
				(merge_map BatSet.empty BatSet.union ty_to_exprs' ty_to_exprs, 
				 merge_map BatSet.empty BatSet.union ty_to_sigs' ty_to_sigs, 
				 merge_map Expr.Wildcard (fun a b -> b) sig_to_expr' sig_to_expr)
			in
			(* remove recursive components *)
			let ty_to_exprs = 
				let exprs = try BatMap.find desired_ty ty_to_exprs with _ -> BatSet.empty in 
				let exprs' = BatSet.filter (fun e -> not (is_recursive e)) exprs in 
				BatMap.add desired_ty exprs' ty_to_exprs
			in
			(* clean up caches *)
			let _ = Tracelearner.init () in
			BatList.mapi (fun i _ ->
				let pts = [i] in 
				Tracelearner.learn !Options.max_height pts spec (desired_sig, desired_ty) 
					(ty_to_exprs, ty_to_sigs, sig_to_expr)
			) input_values  
		in
		let _ = 
			Tracelearner.library := Tracelearner.compute_library spec ty_to_sigs
		in	
		let _ = trace_vsas := vsas in  
		(* let _ = trace_vsas := Tracelearner.synthesis spec  in   *)
		(* let _ = incr Options.init_trace_comp_size in  *)
		let _ = 
			if depth > !Options.max_height then 
				failwith (Printf.sprintf "No solution within depth of %d." !Options.max_height) 
		in
		let (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
			get_components_of_depth spec (ty_to_exprs, ty_to_sigs, sig_to_expr) (depth, depth + 1)
		in
		if depth < !Options.init_comp_size then
			iter (depth+1) (ty_to_exprs, ty_to_sigs, sig_to_expr)
		else
		let _ =
			let exprs = BatMap.foldi (fun _ exprs acc -> BatSet.union exprs acc) ty_to_exprs BatSet.empty in   
			my_prerr_endline (Printf.sprintf "====== iter : %d ======" depth);
			my_prerr_endline (Printf.sprintf "# components: %d" (BatSet.cardinal exprs));
			my_prerr_endline (Printf.sprintf "components: %s" (string_of_set Expr.show exprs)); 
		in 
		try
			let sol =
				main_loop spec (desired_sig, desired_ty) (ty_to_exprs, ty_to_sigs, sig_to_expr)
			in
			wrap spec sol 
		with NoSolInVSA -> (* no solution found *) 
			iter (depth + 1) (ty_to_exprs, ty_to_sigs, sig_to_expr) 
	in
	try
		(* let _ = trace_vsas := Tracelearner.synthesis spec  in   *)
		iter 1 (ty_to_exprs, ty_to_sigs, sig_to_expr)
	with Generator.SolutionFound sol ->
	(* a solution is found while generating components *) 
		wrap spec sol  
