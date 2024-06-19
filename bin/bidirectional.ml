open Specification
open Expr
open Vocab
open BidirectionalUtils
open Generator

let block_vsas : vsa list ref = ref []

module Candidate = 
struct
	(* usable unconstructors in place of a hole, 
		 e.g., match x with S _ -> hole_1 
		 in place of hole_1, S^{-1}(x) is usable *)
	type available_uncons = Expr.t BatSet.t

	(* address of a hole *)
	type addr = int list 
	[@@deriving eq]
	(* indices of input-output examples to be satisfied by a hole *)
	type points = int list 
	[@@deriving eq]
	(* subproblem to be solved by a hole *)
	type subgoal = points * signature * Type.t 
	[@@deriving eq]
	(* candidate and subproblems *)
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
		
		let n_subgoals1 = List.length subgoals_info1 in 
		let n_subgoals2 = List.length subgoals_info2 in 

		let e1_score = cost_of_expr e1 in 
		let e2_score = cost_of_expr e2 in 

		(* the fewer matches, the better *)
		if e1_match_depth <> e2_match_depth then e1_match_depth - e2_match_depth
		else 
			(* the fewer holes, the better *)
			if n_subgoals1 <> n_subgoals2 then n_subgoals1 - n_subgoals2 
			else 
				(* prioritize more likely candidates *)
				if e1_score <> e2_score then e1_score - e2_score
				else 
					(* prioritize smaller candidates *)
					if e1_size <> e1_size then e1_size - e2_size 
					else 
						(* prioritize shorter candidates *)
						if e1_height <> e2_height then e1_height - e2_height
						else  
							Stdlib.compare t1 t2 

end

module CandidateHeap = BatHeap.Make (Candidate) 

(* plug a given expr into a specific position of a candidate hypothesis *)
let plug candidate (addr, expr) =
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


(* among components, return recursive ones with valid unconstructors *)	
let get_valid_recursive_components keyargs desired_ty ty_to_exprs available_uncons = 
	let exprs = try BatMap.find desired_ty ty_to_exprs with _ -> BatSet.empty in
	exprs 
	|> BatSet.filter (fun e -> using_allowed_unconstructor e available_uncons)
	|> BatSet.filter (fun e -> 
			let call_exprs = get_recursive_calls e in
			if BatSet.is_empty call_exprs then false
			else
				BatSet.for_all (function App (_, arg_exp) -> 
					let es = 
						match arg_exp with 
						| Tuple es -> es
						| _ -> [arg_exp]
					in
				let _ = my_prerr_endline (Printf.sprintf "checking %s" (Expr.show arg_exp)) in
				if List.length es = 1 then 
					is_decreasing_expr arg_exp 
				else
					BatSet.exists (fun i -> 
						let e = List.nth es i in 
						let _ = my_prerr_endline (Printf.sprintf "decreasing? %d %s" i (string_of_bool (is_decreasing_expr ~idx:(Some i) e))) in
						is_decreasing_expr ~idx:(Some i) e 
					) keyargs 
				| _ -> assert false
				) call_exprs
		)

let rec learn_funcs = [learn_ctor; learn_unctor; learn_tuple; learn_proj; learn_app; learn_match]

(* An entry to the inference rues for Deduce (Fig. 3) *)
(* pts : indices of IO-examples which should be satisfied 
	 candidate : current incomplete program 
	 addr : address of the hole to be filled *)
and learn candidate addr available_uncons pts spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	let sigs = 
		try 
			BatMap.find desired_type ty_to_sigs
			|> BatSet.filter (fun sg -> 
					let expr = try BatMap.find sg sig_to_expr with _ -> assert false in
					(using_allowed_unconstructor expr available_uncons) &&
					(equal_signature (elems_of_indices pts sg) desired_sig_pts)
				)  
		with _ -> BatSet.empty 
	in
	let result = 
		(* there exists at least one (non-recursive) component immediately satisfying the spec *)
		if not (BatSet.is_empty sigs) then 
			(* D_COMPONENT in Fig. 3 *)
			(* if the user wants to find all solutions, use all the components  *)
			if !Options.find_all then 	
				BatSet.fold (fun sg acc -> 
					let expr = try BatMap.find sg sig_to_expr with _ -> assert false in
					if (using_allowed_unconstructor expr available_uncons) then 
						let plugged = plug candidate (addr, expr) in 
						let _ = my_prerr_endline (Printf.sprintf "direct: plugging %s into %s and obtain %s" (Expr.show expr) (Expr.show candidate) (Expr.show plugged)) in 
						BatSet.add (plugged, []) acc
					else acc
				) sigs BatSet.empty 
			
			(* otherwise, choose the component of the smallest score (i.e., most likely) *)
			else
				let expr = 
					let init_expr = BatMap.find (BatSet.choose sigs) sig_to_expr in 
					(* init_expr *)
					BatSet.fold (fun sg min_expr -> 
						let expr = BatMap.find sg sig_to_expr in 
						if (Expr.cost_of_expr expr) < (Expr.cost_of_expr min_expr) then expr 	
						else min_expr
					) sigs init_expr
				in
				let plugged = plug candidate (addr, expr) in 
				let _ = my_prerr_endline (Printf.sprintf "direct: plugging %s into %s and obtain %s" (Expr.show expr) (Expr.show candidate) (Expr.show plugged)) in 
				BatSet.singleton (plugged, [])
		else BatSet.empty
	in
	(* if the goal is to find a solution and there's a satisfing component, return it *)
	if (not !Options.find_all) && (not (BatSet.is_empty result)) then result
	else
		(*  add recursive components -- angelically assuming recursive expressions may satisfy the goal *)
		(* D_REC in Fig. 3 *)
		let rec_exprs = 
			let keyargs = get_keyargs candidate in 
			get_valid_recursive_components keyargs desired_type ty_to_exprs available_uncons
		in
		let result = 
			BatSet.fold (fun rec_expr acc ->
				let plugged = plug candidate (addr, rec_expr) in 
				let _ = my_prerr_endline (Printf.sprintf "direct: plugging recursive %s into %s and obtain %s" (Expr.show rec_expr) (Expr.show candidate) (Expr.show plugged)) in 
				BatSet.add (plugged, []) acc
			) rec_exprs result
		in
		(* add other hypotheses using other rules *)
		let result = 
			List.fold_left (fun acc learn_func ->
				let result = 
					learn_func rec_exprs candidate addr available_uncons pts spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
				in
				BatSet.union result acc 
			) result learn_funcs
		in 
		result 	  

(* D_CTOR in Fig. 3 *)
and learn_ctor _ candidate addr available_uncons pts spec (desired_sig, _) _ = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_ctor: %s" (string_of_signature desired_sig_pts)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	(* 1. type check : desired output 이 모두 동일한 constructor 꼴인지 (C(v11,v12), .., C(vk1,vk2)) *)
	(* Constructor 때내고 각각 learn 한 후 vsa 구성 *)
	let constructors = 
		List.fold_left (fun s v -> match v with CtorV (i, _) -> BatSet.add i s | _ -> s) BatSet.empty desired_sig_pts 
	in
	let is_of_all_same_constructors = (BatSet.cardinal constructors) = 1 in
	if is_of_all_same_constructors then
		let constructor = BatSet.choose constructors in 
		(* to prevent repeated generation of subproblems like  Un_Cons (Cons ...) *)
		let parent_expr = 
			if (BatList.is_empty addr) then Wildcard 
			else get_expr_from_addr candidate (BatList.remove_at ((List.length addr) - 1) addr) 
		in 
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

(* D_DTOR in Fig. 3 *)	
and learn_unctor _ candidate addr available_uncons pts spec (desired_sig, desired_type) _ = 
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
	
(* D_TUPLE in Fig. 3 *)	
and learn_tuple _ candidate addr available_uncons pts _ (desired_sig, desired_type) _ = 
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

(* D_PROJ in Fig. 3 *)	
and learn_proj _ candidate addr available_uncons pts _ (desired_sig, _) (_, _, sig_to_expr) =
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_proj: %s" (string_of_signature desired_sig_pts)) in
	(* desired output: v1, ..., vk 
	   desired type = T
		 desired_sig_pts : v_a, v_b *)
	(* there is a type ty = Tuple (..., T, ...) (T is i-th element of Tuple) 
	-> Proj (i, Tuple(..., ei, ...)) 
		 a,b-th elements of [[ei]] are v_a, v_b *)
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
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
					(* if this component's output is tuples whose i'th elem is i'th elem of the desired sig,
						the component is the desired one. *)
					if (equal_signature sg_pts_proj_i desired_sig_pts) then
						let plugged = plug candidate (addr, Proj (i, expr)) in 
						BatSet.add (plugged, []) result
					else result  
				) result (BatList.range 0 `To (tuple_len - 1))  
	) sig_to_expr BatSet.empty  
	
(* D_MATCH in Fig. 3 *)	
and learn_match _ candidate addr available_uncons pts spec (desired_sig, desired_type) 
	(_, ty_to_sigs, sig_to_expr) =
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
					let variants = Type.destruct_variant resolved_ty in
					let init_pat2pts = 
						List.fold_left (fun m (i, _) -> 
							let pat = Pattern.Ctor (i, Pattern.Wildcard) in
							BatMap.add pat [] m 
						) BatMap.empty variants
					in 
					BatSet.fold (fun sg branching_infos ->
						let scrutinee = try BatMap.find sg sig_to_expr with _ -> assert false in
						(* invalid scrutinee that uses unallowed unconstructors or 
							does not involve parameter variable x or 
							of recursive call
							(we do not allow inside-out recursion)
							어차피 ty_to_sigs 에는 recursive component 없음 *)
						if (not (using_allowed_unconstructor scrutinee available_uncons)) ||
							(not (contains_id target_func_arg scrutinee)) ||
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
									) init_pat2pts (List.combine sg_pts pts) 
								in
								BatMap.foldi (fun pat pts branches ->
									branches @ [(pat, pts)]   
								) pat2pts []
							in
							(* sort branches : important! -- processing base cases first *)
							let branches =
								BatList.fast_sort (fun (pat1, _) (pat2, _) ->  Pattern.my_compare pat1 pat2 spec.vc) branches
							in 
							BatSet.add (scrutinee, branches) branching_infos	  
					) sigs branching_infos 
				else branching_infos
			| _ -> branching_infos  
		) ty_to_sigs BatSet.empty  
	in 
	let branching_infos = 
		let branching_infos' = 
			(* matches with scrutinees covering all variants *)
			BatSet.filter (fun (_, branches) -> 
				List.for_all (fun (_, pts) -> not (BatList.is_empty pts)) branches 
			) branching_infos 
		in 
		(* if no such matches exist due to lack of I/O examples, just put any expr (satisfying the first I/O example) 
			 on the non-covered branches *)
		if BatSet.is_empty branching_infos' && parent_expr = Wildcard then 
			branching_infos 
			|> set_map (fun (scrutinee, branches) -> 
					let branches' = List.map (fun (pat, pts) -> (pat, if BatList.is_empty pts then [0] else pts)) branches in 
					(scrutinee, branches')
				)
		else branching_infos'
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
					let available_uncons = BatSet.add (Unctor(i, scrutinee)) available_uncons in
					(* ind + 1 because 0 is reserved for scrutinee *)
					let addr' = addr @ [ind + 1] in 
					(addr', available_uncons, (pts, desired_sig, desired_type))
				| _ -> assert false
			) branches
		in
		BatSet.add (plugged, candidate_infos) result
	) branching_infos BatSet.empty


(* D_EXTCALL in Fig. 3 *)
(* learn app : user-defined function fuzzing *)
(* library: value -> (value (closure) * (value list)) list) *)
and learn_app rec_exprs candidate addr available_uncons pts spec (desired_sig, desired_type) 
		(_, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_app : (%s)-th of %s" (string_of_list string_of_int pts) (string_of_signature desired_sig)) in
	let _ = my_prerr_endline (Printf.sprintf "available uncons : %s" (string_of_set show available_uncons)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	(* recursive functions *)
	let inputs = List.map fst spec.spec in
	let output_ty = snd spec.synth_type in
	let rec_exprs = 
		BatSet.elements rec_exprs
	in
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
						BatSet.add (plugged, []) result
				) BatSet.empty rec_exprs 
	in
	let result_lib = 
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
						(* recursive call : signature = [T, T, ..., T] *)
						if (List.for_all is_wildcard_value fun_sig) then result
						else 
						let fun_expr = try BatMap.find fun_sig sig_to_expr with _ -> assert false in
						let arg_exprs_before_cartesian = 
							BatList.mapi (fun arg_index arg_ty ->
								let arg_sigs = try BatMap.find arg_ty ty_to_sigs with _ -> BatSet.empty in
								let arg_exprs = 
									BatSet.fold (fun arg_sig arg_exprs -> 
										let arg_expr = try BatMap.find arg_sig sig_to_expr with _ -> assert false in
										let okay = 
											(using_allowed_unconstructor arg_expr available_uncons) &&
											List.for_all (fun pt -> 
												let desired_output = List.nth desired_sig pt in 
												let arg_output = List.nth arg_sig pt in
												let funcv = (List.nth fun_sig pt) in 
												if (BatMap.mem desired_output !Tracelearner.library) then 
													(* D_EXTCALL1 in Section 5.5 *)
													(* library: value -> (closure * fun_type * (arg value list)) list) *)
													let funv_ty_argvs = BatMap.find desired_output !Tracelearner.library in 
													List.exists (fun (funcv', fun_ty', argvs) ->  
														(Type.equal fun_ty' fun_ty) && (Expr.equal_value funcv' funcv) &&
														(Expr.equal_value (List.nth argvs arg_index) arg_output)
													) funv_ty_argvs
												else false 
											) pts 
										in
										if !Options.no_invmap || okay then 
											arg_expr :: arg_exprs 
										else arg_exprs 
									) arg_sigs []
								in 
								if (Type.equal output_ty arg_ty) then
									arg_exprs 
									@ rec_exprs (* D_EXTCALL2 in Section 5.5 *)
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

(* candidate generation in Algo. 1 *)
let update_heap available_depth candidate_info heap spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	let inputs = List.map fst spec.spec in
	let next_candidate_infos = 
		let (next_candidate, hole_infos) = candidate_info in 
		if (BatList.is_empty hole_infos) then 
			BatSet.empty 
		else 
			let (addr, available_uncons, (pts, desired_sig, desired_type)) = List.hd hole_infos in 
			(* remaining holes *)
			let hole_infos' = List.tl hole_infos in 
			(* process the hole; hole may be filled with an expression, or other holes may be generated from it *)
			let expanded_result = 
				(* already consumed the available depth *)
				if (List.length addr) > available_depth then BatSet.empty 
				else 
					learn next_candidate addr available_uncons pts spec 
								(desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
			in
			BatSet.fold (fun (next_candidate, hole_infos) next_candidate_infos -> 
				let _ = 
					my_prerr_endline (Printf.sprintf "added next_candidate: %s" (Expr.show next_candidate))
				in
				(* newly generated holes + remaining holes *)
				let new_hole_infos = hole_infos @ hole_infos' in 
				(* false if it is not block consistent *)
				let can_be_added = 
					(* if non-recursive or no holes to be filled, no need to do unfolding *)
					if !Options.no_filter || (not (is_recursive next_candidate)) || (BatList.is_empty new_hole_infos) then true
					else 
						let _ = 
							my_prerr_endline (Printf.sprintf "through unfolding, checking feasibility of %s" (Expr.show next_candidate)) 
						in
						let feasible =
							BatList.for_all
							 (fun pt -> 
								(* vsa of blocks satisfying pt-th I/O example *)
								let block_vsa = (List.nth !block_vsas pt) in
								(* p-th input example *)
								let input = List.nth inputs pt in 
								(* the size of the largest block *)
								let upper_bound = snd (pgm_size_of_vsa block_vsa) in 
								try
									(* do unfolding to obtain an open block from the candidate *)
									let block_expr = 
										concolic_eval spec upper_bound next_candidate input 
									in 
									let _ = 
										my_prerr_endline (Printf.sprintf "block expr: %s" (Expr.show block_expr)) 
									in
									(* do matching to check if the candidate is trace consistent *)
									let matched = match_expr_vsa block_expr block_vsa in
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
				(* the candidate is trace consistent *)
				if can_be_added then 
					(* sort the remaining holes: to process the leftmost hole in the smallest candidate program first *)
					let new_hole_infos = BatList.fast_sort (fun (addr1,_,_) (addr2,_,_) -> Stdlib.compare addr1 addr2) new_hole_infos in 
					let _ = my_prerr_endline (Printf.sprintf "added to the queue: %s" (Expr.show next_candidate)) in
					BatSet.add (next_candidate, new_hole_infos) next_candidate_infos 
				else next_candidate_infos
			) expanded_result BatSet.empty 
	in 
	BatSet.fold CandidateHeap.add next_candidate_infos heap 
	

let main_loop spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let input_values = List.map fst spec.spec in
	(* indices of input-output examples to be satisfied *)
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
			(* termination checking *)
			let termination = 
				let call_exprs = get_recursive_calls next_candidate in
				let keyargs = get_keyargs next_candidate in 
				BatSet.for_all (function App (_, arg_exp) -> 
					let es = 
						match arg_exp with 
						| Tuple es -> es
						| _ -> [arg_exp]
					in
					let _ = my_prerr_endline (Printf.sprintf "checking %s" (Expr.show arg_exp)) in
					if BatSet.is_empty keyargs then 
						let _ = my_prerr_endline (Printf.sprintf "decreasing? %s" (string_of_bool (is_decreasing_expr arg_exp))) in
						is_decreasing_expr arg_exp 
					else
						BatSet.for_all (fun i -> 
							let e = List.nth es i in 
							let _ = my_prerr_endline (Printf.sprintf "decreasing? %d %s" i (string_of_bool (is_decreasing_expr ~idx:(Some i) e))) in
							(is_decreasing_expr ~idx:(Some i) e) || (e = Proj(i, Var target_func_arg))
						) keyargs
				| _ -> assert false
				) call_exprs
			in 
			if not termination then 
				let _ = my_prerr_endline (Printf.sprintf "not terminating") in
				let next_heap = CandidateHeap.del_min heap in 
				iter next_heap 
			else 
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
						spec (ty_to_exprs, ty_to_sigs, sig_to_expr)
				in
				iter next_heap
	in
	iter heap 


(** Main Trio algorithm *)						
let synthesis spec =
	(* input examples *)
	let input_values = List.map fst spec.spec in
	(* output examples (called signature) *)
	let desired_sig = List.map snd spec.spec in
	(* type of output *)
	let desired_ty = snd spec.synth_type in 
	(* map from types to component expressions *)
	let ty_to_exprs = BatMap.empty in
	(* map from types to outputs of components *)
	let ty_to_sigs = BatMap.empty in 
	(* map from signatures (outputs) to components that generate the outputs *)
	let sig_to_expr = BatMap.empty in
	let rec iter depth (ty_to_exprs, ty_to_sigs, sig_to_expr) =
		let _ = 
			if depth > !Options.max_size then 
				failwith (Printf.sprintf "No solution whose size is smaller than %d." !Options.max_size) 
		in
		let vsas =
			(* clean up caches *)
			let _ = Tracelearner.init () in
			(* construct version spaces of blocks *)
			BatList.mapi (fun i _ ->
				(* indices of I/O examples to be satisfied *)
				let pts = [i] in 
				Tracelearner.learn !Options.max_height_vsa pts spec (desired_sig, desired_ty) 
					(ty_to_exprs, ty_to_sigs, sig_to_expr)
			) input_values  
		in
		my_prerr_endline (Printf.sprintf "Block expressions are learned");
		(* print blocks (it may crash when blocks are so many ) *)
		if !Options.print_traces then 
			BatList.iteri (fun i vsa ->
				let exprs = set_of_vsa vsa in
				BatSet.iter (fun e ->
					prerr_endline (Printf.sprintf "%s [%d]" (Expr.show (normalize e)) i)
				) exprs
			) vsas;
		(* compute inverse maps *)
		let _ = 
			Tracelearner.library := Tracelearner.compute_library spec ty_to_sigs
		in	
		my_prerr_endline (Printf.sprintf "Inverse maps are obtained");
		let _ = block_vsas := vsas in  
		(* generate components via bottom-up enumeration *)
		let (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
			get_components_of_depth spec (ty_to_exprs, ty_to_sigs, sig_to_expr) (depth, depth + 1)
		in
		(* need to generate more components *)
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
		iter 1 (ty_to_exprs, ty_to_sigs, sig_to_expr)
	with Generator.SolutionFound sol ->
	(* a solution is found while generating components *) 
		wrap spec sol  
