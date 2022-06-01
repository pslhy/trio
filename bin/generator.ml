open Specification
open Expr
open Vocab

type signature = Expr.value list
[@@deriving eq]

let is_top_signature signature =
	List.for_all (equal_value WildcardV) signature  

let string_of_signature signature = 
	string_of_list show_value signature
		
let wrap spec e =
	let from_ty, to_ty = (fst spec.synth_type, snd spec.synth_type) in 
	let p = (target_func_arg, from_ty) in   
	Fix(target_func, Type.Arrow(from_ty, to_ty), 
		Func(p, e)
	)
	
let compute_signature_simple ?(input_values=[]) spec e =
	let input_values = 
		if BatList.is_empty input_values then List.map fst spec.spec 
		else input_values
	in	 
	let eval_context = spec.ec in
	let result =  
		(* make it a function call *)
		let e = wrap spec e in 
  	List.map (fun input_value ->
  		safe_evaluate_with_context eval_context (App(e, exp_of_value input_value))  
  	) input_values   
	in
	result 
	
exception SolutionFound of Expr.t 

(* Helper functions *)
let add_signature ty signature ty_to_sigs =
	let sigs = try BatMap.find ty ty_to_sigs with _ -> BatSet.empty in  
	BatMap.add ty (BatSet.add signature sigs) ty_to_sigs

let add_expr ty expr ty_to_exprs = 
	let exprs = try BatMap.find ty ty_to_exprs with _ -> BatSet.empty in 
	BatMap.add ty (BatSet.add expr exprs) ty_to_exprs 


let is_structurally_decreasing spec e =	 
	let input_values = List.map fst spec.spec in
	let rec_calls = get_recursive_calls e in
	(* prerr_endline ("structurally decreasing? " ^ (Expr.show e)) ;
	prerr_endline (string_of_set Expr.show rec_calls) ; *)
	BatSet.for_all (fun rec_call_exp ->
		let arg_exp = 
			match rec_call_exp with 
			| App (_, e) -> e
			| _ -> assert false 
		in
		(* prerr_endline ("arg_exps " ^ (string_of_set Expr.show arg_exps)) ; *)
		(* BatList.for_all (fun (arg_exp, i) -> *)
			(* no allowed: f (f ...) *)
			if is_recursive arg_exp then 
				false 
			else 
      	let signature = compute_signature_simple spec arg_exp in
				let decreasing = List.for_all2 lt_value signature input_values in
				(* prerr_endline ("arg_exp: " ^ (Expr.show arg_exp)) ;                                      
				prerr_endline ("signature: " ^ (string_of_list show_value signature)) ;                  
				prerr_endline ("input_values: " ^ (string_of_list show_value input_values)) ;             
				prerr_endline ("result < input_values: " ^ (string_of_bool decreasing));                 
				prerr_endline ("contains_id: " ^ (string_of_bool (contains_id target_func_arg arg_exp))); *)
				decreasing && (contains_id target_func_arg arg_exp)   
			 
			(* all constructor sub-expressions of arg_exp do not include target_func_arg *)
			(* let contructors = get_constructors arg_exp in   *)
			(* BatSet.for_all (fun constructor ->              *)
			(* 	not (contains_id target_func_arg constructor) *)
			(* ) contructors                                   *)
			
			(* let unconstructors = get_unconstructors arg_exp in *)
			(* not (BatSet.is_empty unconstructors)               *)
			
			(* BatSet.exists (fun unconstructor ->           *)
			(* 	(contains_id target_func_arg unconstructor) *)
			(* ) unconstructors                              *)
		(* ) arg_exps *)
	) rec_calls
			

let rec is_match_with_basecase e = 
	match e with 
	| Match (_, patterns) ->
		if (BatList.is_empty patterns) then true
		else 
			let rec_calls_in_branches = 
				List.map (fun (p, e) -> get_recursive_calls e) patterns 
			in
			(List.exists BatSet.is_empty rec_calls_in_branches) 
			(* && 
			(List.for_all (fun (p, e) -> is_match_with_basecase e) patterns) *)
	| _ -> true 		 
			 
						
let is_rec_runnable spec e = 
	match e with 
	| Match _ ->
		(is_match_with_basecase e) 
		&& 
		(is_structurally_decreasing spec e)
	| _ -> false  
	
	
let is_runnable spec e = 
	if (count_recursions e) = 0 then true 
	else 
		is_rec_runnable spec e 
		
		
let compute_signature ?(result_top=[]) spec input_values e =
	(* let _ =                                                           *)
	(* 	my_prerr_endline (Printf.sprintf "evaluating %s" (Expr.show e)) *)
	(* in                                                                *)
	(* let eval_context = spec.ec in *)
	let result =  
  	if not (is_runnable spec e) then
  		if BatList.is_empty result_top then 
  			BatList.make (List.length input_values) WildcardV
  		else result_top
  	else  
			compute_signature_simple ~input_values:input_values spec e 
	in
	(* let _ =                                                                                                   *)
	(* 	my_prerr_endline (Printf.sprintf "[[ %s ]] = %s" (Expr.show e) (string_of_list Expr.show_value result)) *)
	(* in                                                                                                        *)
	result

	
let concolic_eval spec upper_bound (orig_expr : t) (input : value) : t = 
	if not (is_runnable spec orig_expr) then failwith "not runnable"
	else 
	(* let _ = my_prerr_endline ("concolic_eval: " ^ (show orig_expr) ^ " upper_bound : " ^ (string_of_int upper_bound)) in *)
	(* let evaluated_so_far = ref BatSet.empty in  *) (* a temporary expediment to avoid non-termination, which is SO bad -- extremely expensive *)
	(* let cnt = ref 0 in  *)
	let rec concolic_eval_sub upper_bound e = 
		(* let _ = 
			incr cnt;
			if (!cnt > !Options.concolic_eval_threshold) then failwith "possibly infinite loop!"
		in *)
		(* let _ = if (BatSet.mem e !evaluated_so_far) then failwith "infinite loop!" else () in *)
		(* let _ = my_prerr_endline ("concolic_eval_sub [" ^ (string_of_int upper_bound) ^ "] : " ^ (show e)) in *)
		let e_size = 
			match e with 
			| Match (_, patterns) -> 
				List.fold_left (fun acc (_, e') -> if not (is_recursive e') then max acc (size_of_expr e') else acc) (-1) patterns
			| _ -> size_of_expr e
		in 
		let is_recursive = (is_recursive e) && (not (is_match_exp e)) in
		if (not is_recursive) && (upper_bound <= 0 || e_size > upper_bound) then Wildcard
			(* failwith "concolic_eval: expression too big" *)
		else 
		(* let _ = if is_match_exp e && (Expr.equal !prev_match e) then failwith "concolic_eval: infinite loop" else () in
		let _ = if is_match_exp e then prev_match := e else () in *)
		let result = 
			match e with
			| App (Var i, e2) when (BatString.equal i target_func) ->
				begin 
				(* check if the argument is executable; if not, it will raise an exception *)
				let _ = evaluate (replace target_func_arg (exp_of_value input) e2) in
				match e2 with 
				| Tuple arg_exps -> 
					BatList.fold_lefti (fun acc i arg_exp -> 
						let src_exp = Proj(i, Var target_func_arg) in 
						let acc = replace_expr src_exp arg_exp acc in
						(* let _ = my_prerr_endline ("after replace: " ^ (show acc)) in *)
						acc
					) orig_expr arg_exps |> concolic_eval_sub upper_bound
				| _ -> 
					let src_exp = Var target_func_arg in 
					replace_expr src_exp e2 orig_expr |> concolic_eval_sub upper_bound
				end
			| App (e1, e2) ->
				let e1 = concolic_eval_sub (upper_bound - 1) e1 in
				let e2 = concolic_eval_sub (upper_bound - 1) e2 in 
				App (e1, e2)
				(* begin 
					match e1 with
					| Func ((i,_),e1) ->
						let e2 = concolic_eval_sub (upper_bound - 1) e2 in 
						concolic_eval_sub (upper_bound - 1) (replace i e2 e1) 
					| Wildcard -> Wildcard
					| _ -> failwith "nonfunc applied"
				end *)
			| Eq (b,e1,e2) ->
				Eq (b, concolic_eval_sub (upper_bound - 2) e1 , concolic_eval_sub (upper_bound - 2) e2)
			| Func (a,e) -> Func(a, concolic_eval_sub (upper_bound - 2) e) 
			| Ctor (i,e) ->
				Ctor (i, concolic_eval_sub (upper_bound - 2) e) 
			| Match (e,branches) as match_expr ->
				let v = (replace target_func_arg (exp_of_value input) e) |> replace_holes spec.ec |> evaluate in
				let bindings_branchexp_opt : ((string * value) list * t) option list =
					List.map (fun (p,branch_e) ->
						try 
							Some ((matches_pattern_and_extractions p v), branch_e)
						with InvalidPatternMatch -> None  
					) branches
				in
				let (_,branch_e) =
					if List.for_all (BatOption.is_none) bindings_branchexp_opt then
						let _ = my_prerr_endline ((show_value v) ^ " not matched: \n " ^ (show match_expr)) in
						failwith ((show_value v) ^ " not matched: \n " ^ (show match_expr))
					else 
						List.find BatOption.is_some bindings_branchexp_opt |> BatOption.get
				in
				concolic_eval_sub upper_bound branch_e 
			| Fix _  -> assert false 
				(* concolic_eval_sub upper_bound (replace i e e') *)
			| Tuple es ->
				Tuple (List.map (fun e' -> concolic_eval_sub (upper_bound - 1) e') es)
			| Proj (i,e) ->
				Proj (i, concolic_eval_sub (upper_bound - 2) e)
			| Unctor (i,e) ->
				Unctor (i, concolic_eval_sub (upper_bound - 2) e)
			| _ -> e 
		in
		(* let _ = evaluated_so_far := BatSet.add result !evaluated_so_far in *)
		result
	in
	(* try *)
		concolic_eval_sub upper_bound orig_expr
		(* never can be matched with anything *)
	(* with _ -> Var ""  *)
	 	
let make_generator arg_exps_list =
	let init_indices = BatList.make (List.length arg_exps_list) 0 in 
	let curr_indices = ref init_indices in 
	let upper_bounds = List.map (fun arg_exps -> List.length arg_exps) arg_exps_list in
	let finished = ref false in  
	let generate_function : unit -> Expr.t list =
		fun () ->
		begin   
			let _ = if !finished then raise BatEnum.No_more_elements in 
			(* let _ = prerr_endline ("before curr " ^ (string_of_list string_of_int !curr_indices)) in  *)
			(* let _ = prerr_endline ("upper_bounds " ^ (string_of_list string_of_int upper_bounds)) in  *)
			let result = 
  			List.map (fun (arg_exps, index) -> 
					try
						List.nth arg_exps index
					with _ -> failwith ((string_of_int (List.length arg_exps)) ^ " " ^ (string_of_int index))
				) (List.combine arg_exps_list !curr_indices)
			in
			(* increment indices *)
			let carry, next_indices = 
				List.fold_left (fun (carry, next_indices) (index, ub) ->
					let carry', index' = 
						if index + carry >= ub then (1, 0) 
						else (0, index + carry)
					in 
					(carry', next_indices@[index'])
				) (1, []) (List.combine !curr_indices upper_bounds)
			in
			(* let _ = prerr_endline ("carry " ^ (string_of_int carry)) in                             *)
			(* let _ = prerr_endline ("after curr " ^ (string_of_list string_of_int next_indices)) in  *)
			let _ =
				if carry = 1 then
					finished := true 
				else
					curr_indices := next_indices 
			in			
			result
		end  
	in
	BatEnum.from generate_function
		
let is_solution desired_sig signature e = 
	(equal_signature desired_sig signature)
 
(* result_ty_arg_tys_arg_expss_set: set of (result_type, possible arg types, list of possible arg expressions ) *)
let grow target_size
			desired_sig spec 
			(result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t) 
			(plug: Expr.t list -> Expr.t list) (* argument expressions -> final expressions *)
			(ty_to_exprs, ty_to_sigs, sig_to_expr) =
	let input_values = List.map fst spec.spec in
	let result_bot = BatList.make (List.length input_values) Bot in
	let result_top = BatList.make (List.length input_values) WildcardV in 
	let (ty_to_exprs_ref, ty_to_sigs_ref, sig_to_expr_ref) = 
		(ref ty_to_exprs, ref ty_to_sigs, ref sig_to_expr)
	in
	BatSet.iter (fun (result_ty, arg_tys, arg_exps_list) ->
		let arg_exps_list : (Expr.t list) list =
			if BatList.is_empty arg_exps_list then  
  			List.map (fun ty ->
  				try BatMap.find ty ty_to_exprs |> BatSet.elements
  				with _ -> []
  			) arg_tys
			else arg_exps_list 
		in
		if (List.for_all (fun arg_exps -> not (BatList.is_empty arg_exps)) arg_exps_list) then 
  		let generator = make_generator arg_exps_list in
  		try
  			while true do
    			let instances = BatEnum.get_exn generator in
					(* let _ = prerr_endline ("arg exps list: " ^ (string_of_list (fun l -> string_of_list Expr.show l) arg_exps_list)) in  *)
					(* let _ = prerr_endline ("instances : " ^ (string_of_list Expr.show instances)) in                                     *)
					List.iter (fun e ->
						(* let _ = prerr_endline ("candidate : " ^ (Expr.show e)) in   *)
						let result_ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc e in
						(* do not generate recursive call expressions as components *)
						(* if not (is_recursive e) then  *)
    				let signature = 
    					compute_signature ~result_top:result_top spec input_values e
    				in
    				if (is_solution desired_sig signature e) then
    					raise (SolutionFound e)
    				else
      				let sigs = 
								try BatMap.find result_ty !ty_to_sigs_ref 
								with _ -> BatSet.empty 
							in
      				(* 재귀호출 expression 의 sig = result_top  *)
							let new_sig = not (BatSet.mem signature sigs) in 
							(* let runnable = not (equal_signature signature result_top) in  *)
							let invalid = (equal_signature signature result_bot) in
							let is_rec = is_recursive e in                    
							let decreasing = is_structurally_decreasing spec e in
      				(* if (new_sig || not_runnable) && (not invalid) && (terminating) then *)
							(* let _ =                                                                    
								if (is_recursive e) then (
									prerr_endline ("expr : " ^ (Expr.show e));                            
									prerr_endline ("signature : " ^ (string_of_signature signature));              
									prerr_endline ("new_sig? : " ^ (string_of_bool new_sig));
									prerr_endline ("invalid? : " ^ (string_of_bool invalid));              
									prerr_endline ("is_recursive : " ^ (string_of_bool (is_recursive e)));
									prerr_endline ("decreasing : " ^ (string_of_bool decreasing))         
								)                                                                     
							in  *)
							(* if component is new, or recursive and structurally decreasing 
								 for recursive components, ty_to_sigs and sig_to_expr are meaningless
								  *)
							if (Expr.size_of_expr e) > target_size then ()
							else if is_rec then (
								if decreasing then 
									ty_to_exprs_ref := add_expr result_ty e !ty_to_exprs_ref;
							)
							else (
								if new_sig && (not invalid) then 
      					(
      						ty_to_exprs_ref := add_expr result_ty e !ty_to_exprs_ref;
									ty_to_sigs_ref := add_signature result_ty signature !ty_to_sigs_ref;
									sig_to_expr_ref := BatMap.add signature e !sig_to_expr_ref 
								)
							)
					) (plug instances)
  			done
  		with BatEnum.No_more_elements -> ()
	) result_ty_arg_tys_arg_expss_set ;
	(!ty_to_exprs_ref, !ty_to_sigs_ref, !sig_to_expr_ref) 
	
	
let grow_app target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	(* set of (result_type, possible arg types) *)
	let result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t =
		BatMap.foldi (fun ty _ acc -> 
		  if (Type.is_arrow_type ty) then
				(* let (t1, t2) = Type.destruct_arrow ty in  *)
				let (t1, t2) = Specification.st_to_pair ty in
				if Type.is_tuple_type t1 then 
					let arg_tys = Type.destruct_tuple t1 in 
					BatSet.add (t2, ty :: arg_tys, []) acc 
				else 
					BatSet.add (t2, [ty; t1], []) acc 
			else acc
		) ty_to_exprs BatSet.empty 
	in
	let plug instances = 
		let _ = assert ((List.length instances) >= 2) in 
		let fun_exp = (List.hd instances) in 
		let arg_exps = (List.tl instances) in
		(* target function : argument is a single pair *)
		if Expr.equal fun_exp (Var target_func) then 
			if (List.length arg_exps) = 1 then 
				[App (fun_exp, List.hd arg_exps)]
			else
				[App (fun_exp, Tuple arg_exps)]
		else 
			[List.fold_left (fun acc e -> App (acc, e)) fun_exp arg_exps]
		(* let (e1, e2) = (List.nth instances 0, List.nth instances 1) in 
		if is_tuple_exp e2 then 
			[List.fold_left (fun acc e -> App (acc, e)) e1 (Expr.destruct_tuple e2)]
		else 
			[App (e1, e2)]  *)
		(* [App (e1, e2)] 	 *)
	in
	grow target_size desired_sig spec result_ty_arg_tys_arg_expss_set plug (ty_to_exprs, ty_to_sigs, sig_to_expr) 
				

let grow_ctor target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
  (* set of (result_type, possible arg types) *)
	let result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t =
		BatMap.foldi (fun _ (arg_ty, parent_ty) acc ->
			BatSet.add (parent_ty, [arg_ty], []) acc
		) spec.vc BatSet.empty
	in
	let plug instances =
		let _ = assert ((List.length instances) = 1) in
		let arg_exp = List.hd instances in
		let arg_ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc arg_exp in    
		BatMap.foldi (fun i (arg_ty', _) acc ->
			if (Type.equal arg_ty arg_ty') then 
				let e = normalize (Ctor (i, arg_exp)) in  
				e :: acc  
			else acc 
		) spec.vc []  
	in
	grow target_size desired_sig spec result_ty_arg_tys_arg_expss_set plug (ty_to_exprs, ty_to_sigs, sig_to_expr) 	


let grow_unctor target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	(* set of (result_type, possible arg types) *)
	let result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t =
		BatMap.foldi (fun _ (arg_ty, parent_ty) acc ->
			(* parent_ty -> C(arg_ty) *)
			(* nat -> O of [] | S of nat *)
			BatSet.add (arg_ty, [parent_ty], []) acc
		) spec.vc BatSet.empty
	in
	let plug instances =
		let _ = assert ((List.length instances) = 1) in
		let e = List.hd instances in
		let ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc e in    
		BatMap.foldi (fun i (arg_ty, parent_ty) acc ->
			if (Type.equal ty parent_ty) && not (Type.equal Type._unit arg_ty) then
				let e = normalize (Unctor (i, e)) in
				e :: acc  
			else acc 
		) spec.vc []  
	in
	grow target_size desired_sig spec result_ty_arg_tys_arg_expss_set plug (ty_to_exprs, ty_to_sigs, sig_to_expr) 	


let grow_eq target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	(ty_to_exprs, ty_to_sigs, sig_to_expr)

exception SynthMatchFailure 

let grow_match target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	(* (ty_to_exprs, ty_to_sigs, sig_to_expr) *)
	let ty = snd spec.synth_type in
	(* let sigs = try BatMap.find ty ty_to_sigs with _ -> BatSet.empty in    *)
	let input_values = List.map fst spec.spec in
	(* let output_values = List.map snd spec.spec in *)
	(* let result_bot = BatList.make (List.length input_values) Bot in       *)
	let result_top = BatList.make (List.length input_values) WildcardV in
	
	(* match e with 에서 e 에는 *)
	(* - 재귀호출 X *)
	(* - variant type*)
	(* - constructor, match 형태 X  *)
	(* - 입력변수가 껴야 함.  *)
	(* scrutinees: 그러한 e 들과 그 타입 쌍들의 리스트 *)
	let resolve_type ty =
		match ty with
		| Type.Named i ->
			(try BatMap.find i spec.td with _ -> assert false)
		| _ -> ty
	in
	let is_distinguishing e =
		let signature =
		 compute_signature ~result_top:result_top spec input_values e
		in
		let used_ctors =
			List.fold_left (fun acc v ->
				match v with
				| CtorV (i, _) -> BatSet.add i acc
				| _ -> acc
			) BatSet.empty signature
		in
		(BatSet.cardinal used_ctors) > 1
	in
	let scrutinees : (Type.t * Expr.t BatSet.t) list =
		BatMap.foldi (fun ty exprs acc ->
			match ty with
			| Type.Named i ->
				let resolved_ty = resolve_type ty in
				if (Type.is_variant_type resolved_ty) then
					let scrutinees =
						BatSet.filter (fun e ->
							(contains_id target_func_arg e) &&
							(not (is_recursive e)) &&
							(not (is_ctor_exp e)) &&
							(not (is_match_exp e)) &&
							(is_distinguishing e)
						) exprs
					in
					(resolved_ty, scrutinees) :: acc
				else acc
			| _ -> acc
		) ty_to_exprs []
	in
	(* let target_types = [ty] (*domof ty_to_exprs*) in *)
	let target_type = ty in
	let result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t =
		List.fold_left (fun result_ty_arg_tys_arg_expss_set (scrutinee_ty, scrutinees) ->
			let _ = assert (Type.is_variant_type scrutinee_ty) in
  		let its = Type.destruct_variant scrutinee_ty in
  		let n_branches = List.length its in
			(* TODO: XXX: assuming only the first variant is the base type *)
			(* let (base_ctor, _) = List.hd its in *)
			(* let base_pattern = Pattern.Ctor(base_ctor, Pattern.Wildcard) in *)
			let ty_exprs =
				(try BatMap.find target_type ty_to_exprs
				 with _ -> BatSet.empty)
				|> BatSet.elements
			in
			let exprs_for_base =
				List.filter (fun e ->
					not (is_recursive e)
				) ty_exprs
			in
			let scrutinees = BatSet.elements scrutinees in
			let arg_expss =
				 [scrutinees; exprs_for_base] @ (BatList.make (n_branches - 1) ty_exprs)
			in
			(* XXX: hack  - no nested matches *)
			let arg_expss =
				List.map (fun arg_exps -> List.filter (fun e -> not (is_match_exp e)) arg_exps) arg_expss
			in
			(* prerr_endline (Printf.sprintf "%d %d\n" (List.length arg_expss) n_branches); *)
			let _ = assert ((List.length arg_expss) = (n_branches + 1)) in
			BatSet.add
				(target_type, scrutinee_ty :: (BatList.make n_branches target_type),
				arg_expss) result_ty_arg_tys_arg_expss_set
		) BatSet.empty scrutinees
	in
	let plug instances =
		
		let scrutinee = try List.hd instances with _ -> assert false in
		let scrutinee_ty =
			Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc scrutinee
			|> resolve_type
		in
		let its = Type.destruct_variant scrutinee_ty in
		(* prerr_endline (Printf.sprintf "%d %d\n" (List.length instances) (List.length its)); *)
		let branches =
			List.map2 (fun (i, _) expr ->
				let pattern = Pattern.Ctor (i, Pattern.Wildcard) in
				(pattern, expr)
			) its (List.tl instances)
		in
		[Match (scrutinee, branches) ]
	in
	grow target_size desired_sig spec result_ty_arg_tys_arg_expss_set plug (ty_to_exprs, ty_to_sigs, sig_to_expr)
	
	(* (* (scrutinee_ty : Type.Variant _) *)                                            *)
	(* List.fold_left (fun (ty_to_exprs, ty_to_sigs) (scrutinee_ty, scrutinees) ->      *)
	(* 	let _ = assert (Type.is_variant_type scrutinee_ty) in                          *)
	(* 	let its = Type.destruct_variant scrutinee_ty in                                *)
	(* 	let n_branches = List.length its in                                            *)
	(* 	(* For each scrutinee *)                                                       *)
	(* 	BatSet.fold (fun scrutinee (ty_to_exprs, ty_to_sigs) ->                        *)
	(* 		(* For each of possible final types (current types we have) *)               *)
	(* 		List.fold_left (fun (ty_to_exprs, ty_to_sigs) target_ty ->                   *)
	(* 			(* TODO: XXX: assuming only the first variant is the base type *)          *)
	(* 			let (base_ctor, _) = List.hd its in                                        *)
	(* 			let base_pattern = Pattern.Ctor(base_ctor, Pattern.Wildcard) in            *)
	(* 			let exprs_for_base =                                                       *)
	(* 				try                                                                      *)
	(* 					BatMap.find target_ty ty_to_exprs                                      *)
	(* 				with _ -> BatSet.empty |> BatSet.filter (fun e -> not (is_recursive e))  *)
	(* 			in                                                                         *)
	(* 			(* set of (result_type, possible arg types) *)                             *)
  (*     	let result_ty_arg_tys_set : (Type.t * (Type.t list)) BatSet.t =            *)
  (*     		BatSet.singleton (target_ty, (BatList.make (n_branches-1) target_ty))    *)
  (*     	in                                                                         *)
  (*     	let plug instances =                                                       *)
  (*     		let _ = assert ((List.length instances) = (n_branches - 1)) in           *)
	(* 				let branches =                                                           *)
	(* 					List.map (fun ((i, _), branch_expr) ->                                 *)
	(* 						let pattern = Pattern.Ctor (i, Pattern.Wildcard) in                  *)
	(* 						(pattern, branch_expr)                                               *)
	(* 					) (List.combine (List.tl its) instances)                               *)
	(* 				in                                                                       *)
	(* 				BatSet.fold (fun base_exp acc ->                                         *)
	(* 					(Match (scrutinee, (base_pattern, base_exp) :: branches)) :: acc       *)
	(* 				) exprs_for_base []                                                      *)
					  
  (*     	in                                                                         *)
  (*     	grow desired_sig spec result_ty_arg_tys_set plug (ty_to_exprs, ty_to_sigs) *)
	(* 		) (ty_to_exprs, ty_to_sigs) target_types                                     *)
	(* 	) scrutinees (ty_to_exprs, ty_to_sigs)                                         *)
	(* ) (ty_to_exprs, ty_to_sigs) scrutinees                                           *)


let grow_tuple target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	(* set of (result_type, possible arg types) *)
	(* construct tuples for variant types *)
	let result_ty_arg_tys_arg_expss_set : (Type.t * (Type.t list) * (Expr.t list) list) BatSet.t =
		(* 지금까지 계산된 타입들 중 베리언트 타입들 *)
		(* expression들을 scrutinee 로 하고 *)
		(* 각 베리언트 마다 만들어내는 타입은 모든 타입 가능 *)
		BatMap.foldi (fun _ (arg_ty, _) acc ->
			match arg_ty with 
			| Type.Tuple ts -> 
				(* let _ = my_prerr_endline (Printf.sprintf "tuple type: %s" (string_of_list Type.show ts)) in *)
				(* no need to generate units *)
				if BatList.is_empty ts then acc 
				else 
					BatSet.add (arg_ty, ts, []) acc
			| _ -> acc 	 
		) spec.vc BatSet.empty
	in
	(* construct tuples for recursive calls *)
	let input_type = fst spec.synth_type in 
	let result_ty_arg_tys_arg_expss_set = 
		match input_type with 
		| Type.Tuple ts -> BatSet.add (input_type, ts, []) result_ty_arg_tys_arg_expss_set
		| _ -> result_ty_arg_tys_arg_expss_set 
	in 
	let plug instances = let _ = assert ((List.length instances) > 1) in [Tuple instances] in
	grow target_size desired_sig spec result_ty_arg_tys_arg_expss_set plug (ty_to_exprs, ty_to_sigs, sig_to_expr) 		 


let grow_proj target_size desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) =
	let input_values = List.map fst spec.spec in
	let result_bot = BatList.make (List.length input_values) Bot in
	let result_top = BatList.make (List.length input_values) WildcardV in 
	BatMap.foldi (fun ty exprs (ty_to_exprs, ty_to_sigs, sig_to_expr) ->
		match ty with 
		| Type.Tuple arg_types ->
			if BatList.is_empty arg_types then 
				(ty_to_exprs, ty_to_sigs, sig_to_expr)
			else
  			BatSet.fold (fun expr (ty_to_exprs, ty_to_sigs, sig_to_expr) ->
					(* no need to add components of form (e1,..ek).i *)
					if is_tuple_exp expr then (ty_to_exprs, ty_to_sigs, sig_to_expr)
					else
  				List.fold_left (fun (ty_to_exprs, ty_to_sigs, sig_to_expr) i ->
  					let e = Proj (i, expr) in
  					let result_ty = try List.nth arg_types i with _ -> assert false in 
  					let signature = 
    					compute_signature ~result_top:result_top spec input_values e
    				in
    				if (is_solution desired_sig signature e) then
    					raise (SolutionFound e)
    				else
      				let sigs = try BatMap.find result_ty ty_to_sigs with _ -> BatSet.empty in
							let new_sig = not (BatSet.mem signature sigs) in 
							let invalid = (equal_signature signature result_bot) in 
							(* let is_rec = is_recursive e in                     *)
							let decreasing = is_structurally_decreasing spec e in
							(* prerr_endline ("expr : " ^ (Expr.show e));                            
							prerr_endline ("signature : " ^ (string_of_signature signature));              
							prerr_endline ("new_sig? : " ^ (string_of_bool new_sig));
							prerr_endline ("invalid? : " ^ (string_of_bool invalid));               *)
      				(* if (new_sig || not_runnable) && (not invalid) && (terminating) then *)
							
							(* if new_sig && ((not (is_recursive e)) || decreasing) && (not invalid) then 
      					(add_expr result_ty e ty_to_exprs, 
      					 add_signature result_ty signature ty_to_sigs, 
								 BatMap.add signature e sig_to_expr)
  						else (ty_to_exprs, ty_to_sigs, sig_to_expr) *)
							if (Expr.size_of_expr e) > target_size then (ty_to_exprs, ty_to_sigs, sig_to_expr) 
							else if (is_recursive e) && decreasing then
								(add_expr result_ty e ty_to_exprs, ty_to_sigs, sig_to_expr) 
							else if new_sig && (not invalid) then 
								(add_expr result_ty e ty_to_exprs, 
      					 add_signature result_ty signature ty_to_sigs, 
								 BatMap.add signature e sig_to_expr)
							else (ty_to_exprs, ty_to_sigs, sig_to_expr) 
  				) (ty_to_exprs, ty_to_sigs, sig_to_expr) (BatList.range 0 `To ((List.length arg_types) - 1))
  			) exprs (ty_to_exprs, ty_to_sigs, sig_to_expr)
		| _ -> (ty_to_exprs, ty_to_sigs, sig_to_expr)
	) ty_to_exprs (ty_to_exprs, ty_to_sigs, sig_to_expr)
	
	
let enum_bu_search spec =
	let input_values = List.map fst spec.spec in 
	(* type -> Expr.t * int (how many recursive calls exist in e) *)
	let ty_to_exprs = BatMap.empty in 
	(* type -> signature (value list) *)
	let ty_to_sigs = BatMap.empty in
	(* signature -> Expr.t  *)
	let sig_to_expr = BatMap.empty in   
	let desired_sig = List.map snd spec.spec in
	(* for non-runnable expression, signature is [_, ..., _] *)
	let result_top = BatList.make (List.length desired_sig) WildcardV in
	try
		(* 크기 1 짜리 모으기 *)
		let small_exprs = 
			(Tuple []) :: (List.map (fun i -> Var i) (domof spec.tc)) 
		in  
		let (ty_to_exprs, ty_to_sigs, sig_to_expr) =
			List.fold_left (fun (ty_to_exprs, ty_to_sigs, sig_to_expr) e ->
				let ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc e in
				let sg = 
					compute_signature ~result_top:result_top spec input_values e
				in
				let exprs = try BatMap.find ty ty_to_exprs with _ -> BatSet.empty in
				let sigs = try BatMap.find ty ty_to_sigs with _ -> BatSet.empty in   
				let ty_to_exprs = 
					BatMap.add ty (BatSet.add e exprs) ty_to_exprs
				in 
				let ty_to_sigs = 
					BatMap.add ty (BatSet.add sg sigs) ty_to_sigs
				in
				let sig_to_expr = 
					BatMap.add sg e sig_to_expr
				in
				(ty_to_exprs, ty_to_sigs, sig_to_expr)
			) (ty_to_exprs, ty_to_sigs, sig_to_expr) small_exprs  
		in 
		let _ =
			my_prerr_endline (Printf.sprintf "===== iter : 1 =====");
			my_prerr_endline (string_of_map Type.show (fun s -> string_of_set Expr.show s) ty_to_exprs) 
		in
		(* 상향식 나열 시작 *)
		(* 부품생성 모드: f(...) 가 포함된 모든 부품식 값 wildcard *)
		(* 확인모드: 재귀호출 정상 수행 *)
		(* bias: 재귀호출은 2~3번 이하로만 일어나도록 갯수 제한. *)
		(*       structural recursion *)
		(*       브랜치들 중 최소 하나 - base type 인 경우 - 는 재귀호출 없음*)
		(* 	     match e with 에서 e 에는 재귀호출 X *)
		let grow_funcs = 
			[grow_tuple; grow_proj; grow_ctor; grow_unctor; grow_eq; grow_app; (*grow_match*)]
		in
  	let rec iter depth (ty_to_exprs, ty_to_sigs, sig_to_expr) =
			let (ty_to_exprs, ty_to_sigs, sig_to_expr) =
				(* map 은 서로 만들어지는 시그니처가 공유 안되서 문제 있음 *)
				(* let (ty_to_exprs_list, ty_to_sigs_list) =                *)
  			(* 	List.map (fun grow_func ->                             *)
  			(* 		grow_func desired_sig spec (ty_to_exprs, ty_to_sigs) *)
  			(* 	) grow_funcs |> List.split                             *)
				(* in                                                       *)
				(* (merge_maps BatSet.empty BatSet.union ty_to_exprs_list,  *)
				(*  merge_maps BatSet.empty BatSet.union ty_to_sigs_list)   *)
				
				let (ty_to_exprs_list, ty_to_sigs, sig_to_expr) = 
  				List.fold_left (fun (ty_to_exprs_list, ty_to_sigs, sig_to_expr) grow_func ->
  					let (ty_to_exprs', ty_to_sigs, sig_to_expr) = 
							grow_func depth desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr)
						in
						(ty_to_exprs' :: ty_to_exprs_list, ty_to_sigs, sig_to_expr)
  				) ([], ty_to_sigs, sig_to_expr) grow_funcs
				in
				(merge_maps BatSet.empty BatSet.union ty_to_exprs_list, ty_to_sigs, sig_to_expr)
  		in
			(* let (*(ty_to_exprs, ty_to_sigs, sig_to_expr)*)_ =                      *)
			(* 	(* if depth mod 5 = 0 then *)                                        *)
			(* 		grow_match desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr) *)
			(* 	(* else                        *)                                    *)
			(* 	(* 	(ty_to_exprs, ty_to_sigs) *)                                    *)
			(* in                                                                     *)
			let _ =
				my_prerr_endline (Printf.sprintf "===== iter : %d =====" depth);
				my_prerr_endline (string_of_map Type.show (fun s -> string_of_set Expr.show s) ty_to_exprs) 
			in 
			iter (depth + 1) (ty_to_exprs, ty_to_sigs, sig_to_expr)
  	in
		iter 2 (ty_to_exprs, ty_to_sigs, sig_to_expr)
	with SolutionFound sol -> 
		wrap spec sol
		
	