open Specification
open Expr
open Vocab
open Generator

type vsa = Union of vsa BatSet.t 
	| Join of Expr.t * vsa list (* Expr.t: to denote expr kind (all arguments are wildcards) *)  
	| Direct of Expr.t 
	| Empty
	
let vsa_of_vsas vsas =  
	if (BatSet.cardinal vsas) = 1 then 
		BatSet.choose vsas
	else Union vsas
	
(* Wildcard in expr can match with anything *)
let rec match_exprs expr1 expr2 = 
	if (is_wildcard_exp expr1) || (is_wildcard_exp expr2) then true 
	else
		let ekind1 = ekind_of_expr expr1 in 
		let ekind2 = ekind_of_expr expr2 in 
		if Expr.equal ekind1 ekind2 then 
			let children1 = children_of_expr expr1 in 
			let children2 = children_of_expr expr2 in 
			if (List.length children1) = (List.length children2) then 
				BatList.for_all2 match_exprs children1 children2
			else 
				false 
		else 
			false

(* check if there exists s in Subst and e in vsa s.t. s(expr) = e *)			
let rec match_expr_vsa expr vsa =
	if is_wildcard_exp expr then true 
	else 
	match vsa with 
	| Empty -> assert false 
	| Direct e -> 
		match_exprs expr e
	| Union vsas -> 
		let _ = assert (not (BatSet.is_empty vsas)) in 
		BatSet.exists (fun vsa -> match_expr_vsa expr vsa) vsas
	| Join (ekind, vsas) -> 
		let _ = assert (not (BatList.is_empty vsas)) in 
		let ekind' = ekind_of_expr expr in 
		if Expr.equal ekind ekind' then 
			let children = children_of_expr expr in
			let _ = assert ((List.length children) = (List.length vsas)) in
			List.for_all2 match_expr_vsa children vsas
		else 
			false

let join_node_of_exp exp =
	match exp with 
	| Var _ -> Join (Var "", [Direct exp])
	| Wildcard -> Join (Wildcard, [Direct exp])
	| App (e1, e2) -> Join (App (Wildcard, Wildcard), [Direct e1; Direct e2])
	| Func (p, e) -> Join (Func (p, Wildcard), [Direct e])
	| Ctor (i, e) -> Join (Ctor (i, Wildcard), [Direct e])
	| Unctor (i, e) -> Join (Unctor (i, Wildcard), [Direct e])
	| Eq (b, e1, e2) -> Join (Eq (b, Wildcard, Wildcard), [Direct e1; Direct e2])
	| Match (e, patterns) ->
		let patterns_abstract = List.map (fun (p, _) -> (p, Wildcard)) patterns in  
		Join (Match (Wildcard, patterns_abstract), (Direct e) :: List.map (fun (_, e') -> Direct e') patterns)
	| Fix _ -> assert false 
  | Tuple es -> Join (Tuple [], List.map (fun e -> Direct e) es)
  | Proj (i, e) -> Join (Proj(i, Wildcard), [Direct e])	
		  

let union_vsa vsa1 vsa2 = 
	match vsa1, vsa2 with 
	| Empty, _ -> vsa2
	| _, Empty -> vsa1
	| Union vsas1, Union vsas2 ->
		Union (BatSet.union vsas1 vsas2) 
	| Union vsas1, _ -> 
		Union (BatSet.add vsa2 vsas1)
	| _, Union vsas2 -> 
		Union (BatSet.add vsa1 vsas2)
	| _, _ -> 
		Union (BatSet.add vsa1 (BatSet.singleton vsa2))
		  
(* FlashMeta paper Section 4.1 *)
let rec intersect_vsa vsa1 vsa2 = 
	match vsa1, vsa2 with 
	| Empty, _ -> Empty
	| _, Empty -> Empty
	| Direct e1, Direct e2 -> 
		if (Expr.equal e1 e2) then Direct e1 else Empty 
	| Direct _, Union _ -> 
		intersect_vsa (Union (BatSet.singleton vsa1)) vsa2
	| Direct e1, Join _ ->
		intersect_vsa (join_node_of_exp e1) vsa2
	| Join _, Direct e2 ->
		intersect_vsa vsa1 (join_node_of_exp e2)  	 
	| Union vsas1, Union vsas2 ->
		let vsas = 
		 BatSet.fold (fun vsa1 vsas -> 
			BatSet.fold (fun vsa2 vsas ->
				let vsa = intersect_vsa vsa1 vsa2 in 
				if vsa = Empty then vsas 
				else BatSet.add vsa vsas 
			) vsas2 vsas
		 ) vsas1 BatSet.empty
		in 
		if BatSet.is_empty vsas then Empty 
		else Union vsas
	| Join (ekind1, vsas1), Join (ekind2, vsas2) -> 
		if (Expr.equal ekind1 ekind2) && (List.length vsas1) = (List.length vsas2) then
			let vsas = 
				List.map2 (fun vsa1 vsa2 -> intersect_vsa vsa1 vsa2) vsas1 vsas2
			in 
			if List.mem Empty vsas then Empty  
			else Join (ekind1, vsas) 		
		else Empty
	| Union _, _ ->
		intersect_vsa vsa1 (Union (BatSet.singleton vsa2))
	| _, Union _ ->
		intersect_vsa (Union (BatSet.singleton vsa1)) vsa2 
		
let intersect_vsa_list vsa_list = 
	if BatList.is_empty vsa_list then Empty 
	else 
		List.fold_left intersect_vsa (List.hd vsa_list) (List.tl vsa_list) 
				
exception NoSolInVSA
exception VSAFound of vsa BatSet.t
exception LearnFailure
exception LearnMatchFailure
exception SubSolutionFound of Expr.t 

(* return: (ty_to_exprs, ty_to_sigs, sig_to_expr) *)
let get_components_of_depth ?(grow_funcs=[]) spec (ty_to_exprs, ty_to_sigs, sig_to_expr) (curr_depth, max_depth) =
	let input_values = List.map fst spec.spec in 
	let desired_sig = List.map snd spec.spec in
	let result_top = BatList.make (List.length desired_sig) WildcardV in 
	let (ty_to_exprs, ty_to_sigs, sig_to_expr) = 
  	if (curr_depth = 1) then 
  		(* size 1 exprs: variables and unit *)
  		let small_exprs = 
  			(Tuple []) :: (List.map (fun i -> Var i) (domof spec.tc)) 
  		in  
			List.fold_left (fun (ty_to_exprs, ty_to_sigs, sig_to_expr) e ->
				let ty = Typecheck.typecheck_exp spec.ec spec.tc spec.td spec.vc e in
				let sg = 
					compute_signature ~result_top:result_top spec input_values e
				in
				let ty_to_exprs = add_expr ty e ty_to_exprs in 
				let ty_to_sigs = add_signature ty sg ty_to_sigs in
				let sig_to_expr = BatMap.add sg e sig_to_expr in
				(ty_to_exprs, ty_to_sigs, sig_to_expr)
			) (ty_to_exprs, ty_to_sigs, sig_to_expr) small_exprs  
  	else (ty_to_exprs, ty_to_sigs, sig_to_expr) 
	in	
	let grow_funcs = 
		if BatList.is_empty grow_funcs then 
			[grow_tuple; grow_proj; grow_ctor; grow_unctor; grow_eq; grow_app]
		else grow_funcs
	in
	let rec iter depth (ty_to_exprs, ty_to_sigs, sig_to_expr) =
		if depth >= max_depth then 
			(ty_to_exprs, ty_to_sigs, sig_to_expr)
		else
			let (ty_to_exprs, ty_to_sigs, sig_to_expr) =
				let (ty_to_exprs_list, ty_to_sigs, sig_to_expr) = 
  				List.fold_left (fun (ty_to_exprs_list, ty_to_sigs, sig_to_expr) grow_func ->
  					let (ty_to_exprs', ty_to_sigs, sig_to_expr) = 
							grow_func curr_depth desired_sig spec (ty_to_exprs, ty_to_sigs, sig_to_expr)
						in
						(ty_to_exprs' :: ty_to_exprs_list, ty_to_sigs, sig_to_expr)
  				) ([], ty_to_sigs, sig_to_expr) grow_funcs
				in
				(merge_maps BatSet.empty BatSet.union ty_to_exprs_list, ty_to_sigs, sig_to_expr)
  		in
			iter (depth + 1) (ty_to_exprs, ty_to_sigs, sig_to_expr)
	in
	iter curr_depth (ty_to_exprs, ty_to_sigs, sig_to_expr)
	

let rec string_of_vsa vsa = 
	match vsa with 
	| Union vsas -> string_of_set ~first:"{" ~last:"}" ~sep:" U " string_of_vsa vsas 
	| Join (ekind, vsa_lst) -> 
		(Expr.show ekind) ^ (string_of_list ~first:"[" ~last:"]" ~sep:"; " string_of_vsa vsa_lst)   
	| Direct expr -> Expr.show expr 	
	| Empty -> "e" 

let rec pgm_count_of_vsa vsa =
	match vsa with 
	| Direct _ -> 1
	| Join (_, vsa_list) ->
		let sizes = BatList.map pgm_count_of_vsa vsa_list in 
		List.fold_left ( * ) 1 sizes   
	| Union vsa_set -> 
		BatSet.fold (fun vsa acc -> (pgm_count_of_vsa vsa) + acc) vsa_set 0
	| Empty -> 0 
	
(* return (lowerbound, upperbound) of size of programs in vsa *)
let int_max = 9999 
let rec pgm_size_of_vsa vsa =
	match vsa with 
	| Direct expr -> (Expr.size_of_expr expr, Expr.size_of_expr expr)
	| Join (_, vsa_list) ->
		let sizes = BatList.map pgm_size_of_vsa vsa_list in 
		BatList.fold_left (fun (lb, ub) (lb', ub') ->
			(lb + lb', ub + ub') 	 
		) (1, 1) sizes  
	| Union vsa_set -> 
		BatSet.fold (fun vsa' (lb, ub) ->
			let (lb', ub') = pgm_size_of_vsa vsa' in 
			((if (lb' < lb) then lb' else lb),
			 (if (ub' > ub) then ub' else ub)) 	 
		) vsa_set (int_max, -int_max)
	| Empty -> (0, 0) 
		  
let rec choose_best_from_vsa vsa = 
	match vsa with 
	| Direct expr -> expr 
	| Union vsa_set ->
		let _ = assert (not (BatSet.is_empty vsa_set)) in 
		let vsa_list = BatSet.elements vsa_set in 
		let vsa_list_with_size = List.map (fun vsa -> (pgm_size_of_vsa vsa, vsa)) vsa_list in 
		let vsa_list_with_size = 
			(* pick the VSA containing the smallest expr *)
			List.sort (fun ((lb1, _), _) ((lb2, _), _) -> lb1 - lb2) vsa_list_with_size
		in 
		BatList.hd vsa_list_with_size |> snd |> choose_best_from_vsa   
	| Join (ekind, vsa_list) ->
		Expr.construct_from_ekind_and_argexprs ekind (BatList.map choose_best_from_vsa vsa_list)  
	| Empty -> raise NoSolInVSA	 

(* return cost of program in vsa  *)
let rec pgm_cost_of_vsa vsa =
  match vsa with
  | Direct expr -> cost_of_expr expr
  | Join (_, vsa_list) ->
      let costs = BatList.map pgm_cost_of_vsa vsa_list in
      BatList.fold_left (fun c1 c2 -> c1+c2) 0 costs
  | Union vsa_set ->
      BatSet.fold (fun vsa' c -> c + (pgm_cost_of_vsa vsa')) vsa_set 0 
  | Empty -> 0

let rec choose_low_cost_from_vsa vsa = 
  match vsa with 
  | Direct expr -> expr 
  | Union vsa_set ->
    let _ = assert (not (BatSet.is_empty vsa_set)) in 
    let vsa_list = BatSet.elements vsa_set in 
    let vsa_list_with_cost = List.map (fun vsa -> (pgm_cost_of_vsa vsa, vsa)) vsa_list in 
    let vsa_list_with_cost = 
      List.sort (fun (c1, _) (c2, _) -> c1 - c2) vsa_list_with_cost
    in 
    BatList.hd vsa_list_with_cost |> snd |> choose_low_cost_from_vsa   
  | Join (ekind, vsa_list) ->
    Expr.construct_from_ekind_and_argexprs ekind (BatList.map choose_low_cost_from_vsa vsa_list)  
  | Empty -> raise NoSolInVSA 

let rec set_of_vsa vsa =
	match vsa with 
	| Direct expr -> BatSet.singleton expr 
	| Union vsa_set ->
		let _ = assert (not (BatSet.is_empty vsa_set)) in
		BatSet.fold (fun vsa acc ->
			BatSet.union acc (set_of_vsa vsa)  
		) vsa_set BatSet.empty  
	| Join (ekind, vsa_list) ->
		let exprs_list = 
			List.map (fun vsa -> set_of_vsa vsa |> BatSet.elements) vsa_list
			|> BatList.n_cartesian_product
		in 
		List.fold_left (fun acc exprs -> 
			let e = Expr.construct_from_ekind_and_argexprs ekind exprs in 
			BatSet.add e acc 
		) BatSet.empty exprs_list
	| Empty -> BatSet.empty


