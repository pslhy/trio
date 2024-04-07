open Specification
open Expr
open Vocab
open BidirectionalUtils
open Generator

(* This file is for computing block expressions and inverse maps. 
   In the submitted version, we use term "trace" instead of blocks. 
	 The term has been changed at the request of the reviewers 
	 but the term "trace" is still used in the code. *)
	 

(* (int list (points) * signature) -> vsa * depth *)
let learn_cache : (int list * signature, (vsa * int)) BatMap.t ref = ref BatMap.empty
let now_learning = ref BatSet.empty 

(* library: value -> (closure * fun_type * (arg value list)) list) *)
let library : (value, (value * Type.t * value list) list) BatMap.t ref = ref BatMap.empty 
	
(* corresponds to BlockGen in Fig. 4 *)
(* pts : indices of IO-examples which should be satisfied *)
let rec learn available_depth pts spec (desired_sig, desired_type) 
				(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let key = (pts, desired_sig) in 
	let _ = 
		my_prerr_endline (Printf.sprintf "learn [%d]: (%s)-th of %s" available_depth (string_of_list string_of_int pts) (string_of_signature desired_sig));
	in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	(* already consumed available_depth *)
	if (available_depth <= 0) then Empty
	(* to avoid revisiting the same synthesis problem being solved *)
	else if (BatSet.mem key !now_learning) then Empty
	(* already solved it before and the solution is in the cache *)
	else if ( (BatMap.mem key !learn_cache) &&
						let (_, depth) = BatMap.find key !learn_cache in	
  					(depth <= available_depth)
					) 
	then
		let (vsa, _) = BatMap.find key !learn_cache in
		my_prerr_endline ("found in cache!" ^ (if vsa = Empty then " -- empty" else ""));
		vsa
	else
		let _ = 
			now_learning := BatSet.add key !now_learning
		in
		let sigs = 
			try 
				BatMap.find desired_type ty_to_sigs
				|> BatSet.filter (fun sg -> equal_signature (elems_of_indices pts sg) desired_sig_pts)  
			with _ -> BatSet.empty 
		in
		let result = 
			let vsas = 
				(* compute simple blocks -- SimpleBlocks in Fig. 4 *)
  			BatSet.fold (fun sg acc -> 
  				let expr = try (BatMap.find sg sig_to_expr) with _ -> assert false in 
					let _ = 
						my_prerr_endline (Printf.sprintf "Direct: %s" (Expr.show expr)) 
					in 
					BatSet.add (Direct expr) acc
  			) sigs BatSet.empty  
			in
			(* additionally compute compound blocks -- CompoundBlocks in Fig. 4*)
			let vsas = 
				List.fold_left (fun vsas learn_func ->
					let vsa = 
						learn_func available_depth pts spec (desired_sig, desired_type) (ty_to_exprs, ty_to_sigs, sig_to_expr)
					in
					if (vsa = Empty) then vsas
					else BatSet.add vsa vsas 	 
				) vsas learn_funcs
			in 
			if (BatSet.is_empty vsas) then Empty 
			else vsa_of_vsas vsas
		in
		(* add it to the cache *)
		let _ = 
			learn_cache := BatMap.add key (result, available_depth) !learn_cache;
			now_learning := BatSet.remove key !now_learning 
		in 
		result 	  
		
(* B_CTOR in Fig. 4 *)		
and learn_ctor available_depth pts spec (desired_sig, _) 
		(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_ctor [%d]: %s" available_depth (string_of_signature desired_sig_pts)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	(* desired output should be of form (C(v11,v12), .., C(vk1,vk2)) for some constructor C *)
	if (List.for_all (fun v -> is_ctor_value v) desired_sig_pts) then
		let constructors = 
			List.map (fun v -> match v with CtorV (i, _) -> i | _ -> assert false) desired_sig_pts
			|> list2set 
		in
		(* check if only one constructor is used *)
		let is_of_all_same_constructors = (BatSet.cardinal constructors) = 1 in
		if is_of_all_same_constructors then
			let constructor = BatSet.choose constructors in 
			let arg_vsa =
				(* Constructor 때내고 각각 learn 한 후 vsa 구성 *)
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
				learn (available_depth - 1) pts spec (desired_sig', desired_type') 
					(ty_to_exprs, ty_to_sigs, sig_to_expr)
			in
			if arg_vsa = Empty then Empty
			else
				let ekind = Ctor (constructor, Wildcard) in 
				Join (ekind, [arg_vsa])
		else 
			Empty 
	else Empty 		

(* B_DTOR in Fig. 4 *)		
(* C^-1 ( ?? ) = [v1, ... , vn] : desired_type *)
(* ?? => [C(v1), ..., C(vn)]  *)
and learn_unctor available_depth pts spec (desired_sig, desired_type) 
		(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_unctor [%d]: %s" available_depth (string_of_signature desired_sig_pts)) in 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	let constructor_desired_types = 
		(* ctor(v:arg_ty) : parent_ty *)
		BatMap.foldi (fun ctor (arg_ty, parent_ty) acc ->
			if (Type.equal arg_ty desired_type) && (not (Type.equal Type._unit arg_ty)) then
				BatSet.add (ctor, parent_ty) acc 
			else acc 
		) spec.vc BatSet.empty 
	in 
	let vsas = 
  	BatSet.fold (fun (ctor, desired_type') vsas ->
  		let desired_sig' =
  			BatList.mapi (fun i v ->
  				if (List.mem i pts) then CtorV(ctor, v) else v 
  			) desired_sig 
  		in 
			let vsa =
				let arg_vsa =
    			learn (available_depth - 1) pts spec (desired_sig', desired_type') 
    				(ty_to_exprs, ty_to_sigs, sig_to_expr) 
    		in  
				if arg_vsa = Empty then Empty 
				else 
					let ekind = Unctor (ctor, Wildcard) in 
					Join (ekind, [arg_vsa])
			in
			if vsa = Empty then vsas 
			else BatSet.add vsa vsas
  	) constructor_desired_types BatSet.empty 
	in
	if BatSet.is_empty vsas then Empty
	else Union vsas 
		 
(* B_TUPLE in Fig. 4 *)
and learn_tuple available_depth pts spec (desired_sig, desired_type) 
		(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
		(* desired output: TupleV(v11, v12), ... TupleV(vk1, vk2) *)
		(* -> Join(Tuple, learn v11, ..., vk1, learn v12, ..., k2) *)
		let desired_sig_pts = (elems_of_indices pts desired_sig) in
		let _ = my_prerr_endline (Printf.sprintf "learn_tuple [%d]: %s" available_depth (string_of_signature desired_sig_pts)) in
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
			let _ = 
				(* some expr evaluates to tuples of different lengths -- should be impossible *)
				if ((BatSet.cardinal tuple_lens) <> 1) then 
					let _ = prerr_endline (string_of_list show_value desired_sig) in
					let _ = prerr_endline (string_of_list string_of_int pts) in
					let _ = prerr_endline (string_of_list show_value desired_sig_pts) in 
					assert false   
			in
			let tuple_len = BatSet.choose tuple_lens in
			try
				(* empty tuple *)
				let _ = if tuple_len = 0 then raise LearnFailure in 
  			let arg_vsa_list =
  				List.map (fun i ->
  					let desired_sig' =  
      				BatList.mapi (fun i' v ->
  							if List.mem i' pts then (* i'-th output example should be satisfied *)
        					match v with 
        					| TupleV vs -> List.nth vs i (* i-th element of the tuple is the desired output *)
        					| _ -> assert false
  							else v  (* don't care -- any value is fine *)
      				) desired_sig
    				in
  					let desired_type' = List.nth (Type.destruct_tuple desired_type) i in 
  					let arg_vsa =  
      				learn available_depth pts spec (desired_sig', desired_type') 
      					(ty_to_exprs, ty_to_sigs, sig_to_expr)
      			in 
  					let _ = if arg_vsa = Empty then raise LearnFailure in 
  					arg_vsa
  				) (BatList.range 0 `To (tuple_len - 1)) 
  			in
  			let ekind = Tuple [] in 
  			Join (ekind, arg_vsa_list) 
			with LearnFailure -> Empty 
		else Empty 

(* B_PROJ in Fig. 4 *)		
and learn_proj available_depth pts _ (desired_sig, _) 
	(_, _, sig_to_expr) =
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_proj [%d]: %s" available_depth (string_of_signature desired_sig_pts)) in
	(* desired output: v1, ..., vk *)
	(* -> Union_i Join(Proj_i, learn [comp]) *)
	(*      where comp is a component *)
	(* 			with signature = [TupleV(v11, ..., v1n), ... TupleV(vk1, ..., vkn)]  *)
	(* 			and v1i = v1 ,..., vki = vk   *)
	(* TODO: 부품을 쓰기 보다는, wildcard 를 써서 새로운 스펙 만들기 *)	 
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in 
	let vsas =
		BatMap.foldi (fun sg expr vsas ->
			let sg_pts = (elems_of_indices pts sg) in
			(* only consider components whose outputs are tuples *)
			if not (List.for_all is_tuple_value sg_pts) then vsas
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
				if tuple_len = 0 then vsas 
				else 
					List.fold_left (fun vsas i ->
						let sg_pts_proj_i =
							List.map (fun v -> match v with TupleV vs -> List.nth vs i | _ -> assert false) sg_pts 
						in 
						(* if this component's output are tuples whose i'th elem is i'th elem of the desired sig,
							the component is the desired one. *)
						if (equal_signature sg_pts_proj_i desired_sig_pts) then
							let proj_expr = Proj (i, expr) in 
							let _ = 
								my_prerr_endline (Printf.sprintf "Direct: %s" (Expr.show proj_expr)) 
							in 
							BatSet.add (Direct proj_expr) vsas    
						else vsas  
					) vsas (BatList.range 0 `To (tuple_len - 1))  
		) sig_to_expr BatSet.empty  
	in 	
	if BatSet.is_empty vsas then Empty
	else Union vsas 

(* B_APP in Fig. 4 *)
(* learn app : learn VSAs via fuzzing over user-defined functions 
	 target function is not considered *)
(* library: value (output) -> (value (closure) * (value list) (args)) list) *)
and learn_app available_depth pts spec (desired_sig, desired_type) 
		(ty_to_exprs, ty_to_sigs, sig_to_expr) = 
	let desired_sig_pts = (elems_of_indices pts desired_sig) in
	let _ = my_prerr_endline (Printf.sprintf "learn_app [%d]: (%s)-th of %s" available_depth (string_of_list string_of_int pts) (string_of_signature desired_sig)) in
	let _ = assert (not (BatList.is_empty desired_sig_pts)) in
	let vsas_lib =  
		(* construct a VSA for each point and intersect them *)
		List.map (fun pt ->
			let output = List.nth desired_sig pt in
			(* desired output is not in the library. skip *)
			if not (BatMap.mem output !library) then Empty
			else
				let funcv_args_list = BatMap.find output !library in
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
    						learn 1 [pt] spec (desired_sig', fun_ty)
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
        					in
      						let vsa_for_arg =
      							learn (available_depth - 1) [pt] spec (desired_sig', arg_ty)
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
		) pts
	in
	let vsa_lib = intersect_vsa_list vsas_lib in
	vsa_lib 	


and learn_funcs = [learn_ctor; learn_unctor; learn_tuple; learn_proj; learn_app]


(* Section 4.2 Getting Inverse Maps of External Functions by Library Sampling *)
(* library: value (output) -> (closure * type * (value list)) list  (closure, type, arg values) *)
let compute_library spec ty_to_sigs =
	(* size of the largest input value *)
	let inputs : value list = List.map fst spec.spec in 
	let outputs : value list = List.map snd spec.spec in 
	(* collect all user-provided functions and their types 
		 ty_to_sigs contains evaluation results of component expressions *)
	let func_definitions : (value * Type.t) BatSet.t (* closure, type *) =
		BatMap.foldi (fun ty sigs acc ->
			if Type.is_arrow_type ty then
				BatSet.fold (fun sg acc ->
					(* expression involving target function: signature comprises top values 
						 [[ f ]](i1, ..., in) = [T, ..., T] *)
					if (is_top_signature sg) then acc 
					else 
  					List.fold_left (fun acc v ->
							if (is_func_value v) then 
  							BatSet.add (v, ty) acc
							else (* not a function closure *)
								acc	 
  					) acc sg 
				) sigs acc        
			else acc   
		) ty_to_sigs BatSet.empty 
	in
	(* collect inputs for library sampling 
		 use all sub-structures of values that appear in I/O examples 
		 e.g., from S(S(S(O))) (i.e., 3), get S(S(S(O))), S(S(O)), S(O), O (i.e., 3, 2, 1, 0) 
		 and use them as inputs for library function sampling *)
	let ty_to_exprs = 
		let rec get_all_subexpr_in_value v = 
			match v with 
			| CtorV (_, v') -> 
				BatSet.add (exp_of_value v) (get_all_subexpr_in_value v')
  		| TupleV vs -> 
				List.fold_left (fun acc v ->
					BatSet.union (get_all_subexpr_in_value v) acc
				) BatSet.empty vs
			| _ -> BatSet.empty 
		in
		let exprs = 
			List.fold_left (fun acc v -> 
				BatSet.union acc (get_all_subexpr_in_value v)
			) BatSet.empty (inputs @ outputs) 
		in
		BatSet.fold (fun expr ty_to_exprs ->
			let ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc expr in 
			let exprs = try BatMap.find ty ty_to_exprs with _ -> BatSet.empty in 
			BatMap.add ty (BatSet.add expr exprs) ty_to_exprs
		) exprs BatMap.empty 
	in 
	(* another method for getting inputs for library sampling 
		 construct values of height <= max_height of values that appear in I/O examples 
		 we do not use this method for an efficiency issue but we leave this on record *)
	(* let max_height = 
		List.fold_left (fun max_height input ->
			let height = 
				match input with 
				|	TupleV vs -> 
					BatList.max (List.map (fun v -> height_of_expr (exp_of_value v)) vs) 
				| _ -> height_of_expr (exp_of_value input)
			in
			if max_height < height then height else max_height
		) 0 inputs   
	in
	let (ty_to_exprs,_,_) =
		let rec fix depth (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
			let (ty_to_exprs', ty_to_sigs', sig_to_expr') = 
				get_components_of_depth ~grow_funcs:[grow_ctor; grow_tuple] spec (ty_to_exprs, ty_to_sigs, sig_to_expr) (depth, depth + 1)
			in
			if (BatMap.compare BatSet.compare ty_to_exprs' ty_to_exprs) = 0 || depth > max_height then 
				(ty_to_exprs, ty_to_sigs, sig_to_expr)
			else fix (depth + 1) (ty_to_exprs', ty_to_sigs', sig_to_expr')
		in
		fix 2 (BatMap.add Type._unit (BatSet.singleton unit_) BatMap.empty, BatMap.empty, BatMap.empty)
	in *)
	
	(* call the function closures with the collected inputs as arguments *)
	BatSet.fold (fun (funv, ty) lib ->
		let _ = assert (Type.is_arrow_type ty) in
		(* t1 -> t2 -> ... -> tn  => (t1 * t2 * ... * tn-1), tn 
			 t1 -> t2  => t1, t2 *)
		let (arg_ty, _) = Specification.st_to_pair ty in
		(* arg_ty 는 tuple 타입. tuple 하나마다 ty_to_exprs 참조해서 상수 넣음. *)
		let arg_exprs_list = 
			let ts = if Type.is_tuple_type arg_ty then Type.destruct_tuple arg_ty else [arg_ty] in
			(* get all possible arg expressions *)
			let rec exprs_of_type ty =
				match ty with
  			| Type.Tuple ts ->
					(BatList.n_cartesian_product (List.map exprs_of_type ts))
					|> List.map (fun es -> Tuple es)  
  			| _ -> try BatMap.find ty ty_to_exprs |> BatSet.elements with _ -> []  
			in 
			(* arg_ty = (t1, t2, t3) 면 [ty_to_exprs t1, ty_to_exprs t2, ty_to_exprs t3] 을 만들고 *)
			List.map (fun t -> exprs_of_type t) ts
			(* 걔들 cartesian product 구함. [[e1,e2,e3], [e1',e2',e3'], ... ] *)
			|> BatList.n_cartesian_product 	 
		in
		(* [[e1,e2,e3], [e1',e2',e3'], ... ] -> [[v1,v2,v3], [v1',v2',v3'], ... ] *)
		let arg_values_list =
			List.map (fun es -> List.map evaluate es) arg_exprs_list 
		in   
		(* [[e1,e2,e3], ... ] -> [ [[ ((f e1) e2) e3 ]] ; ... *)
		let result_values =
			List.map (fun arg_exprs ->
				let call_exp = 
					List.fold_left (fun abs arg_expr -> App (abs, arg_expr)) (exp_of_value funv) arg_exprs
				in
				try evaluate call_exp with _ -> Bot  
			) arg_exprs_list 
		in 
		(* add v |-> (f, [v1, .., vn]) into the inverse map for each f(v1, .., vn) = v *) 
		List.fold_left2 (fun lib result_value arg_values ->
			let bindings = try BatMap.find result_value lib with _ -> [] in
			let _ =
				my_prerr_endline
					(Printf.sprintf "lib: %s -> %s" (*(show_value funv)*) (string_of_list show_value arg_values) (show_value result_value))
			in
			BatMap.add result_value ((funv, ty, arg_values) :: bindings) lib
		) lib result_values arg_values_list  
	) func_definitions BatMap.empty  
	
let init () = 
	let _ = learn_cache := BatMap.empty in
	let _ = now_learning := BatSet.empty in 
	()
