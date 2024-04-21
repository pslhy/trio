open Vocab

exception InvalidPatternMatch

let target_func = "f"
let target_func_arg = "x"

module Pattern =
struct
  type t =
    | Tuple of t list
    | Ctor of string * t
    | Var of string
    | Wildcard
  [@@deriving eq,ord,show]

	let my_compare t1 t2 vc = 
		(* sort patterns so that base case can be processed first *)
		match t1, t2 with 
		| _, Wildcard -> 1 
		| Wildcard, _ -> -1 
		| Ctor (i1, _), Ctor (i2, _) -> 
			(
			try 
				let (arg_ty1, _) = BatMap.find i1 vc in 
				let (arg_ty2, _) = BatMap.find i2 vc in 
				Type.compare arg_ty1 arg_ty2
			with _ -> failwith "Pattern.compare: something's wrong with vc!"
			)
		| _ -> Stdlib.compare t1 t2 

  let rec contains_id (i:string) (p:t) : bool =
    begin match p with
      | Tuple ps -> List.exists (contains_id i) ps
      | Ctor (_,p) -> contains_id i p
      | Var i' -> String.equal i i'
      | Wildcard -> false
    end

	let rec show t = 
		match t with 
		| Tuple ts -> string_of_list ~first:"[" ~last:"]" ~sep:"," show ts
		| Ctor (i, t) -> Printf.sprintf "%s(%s)" i (show t)
		| Var i -> i 
		| Wildcard -> "_" 
	
end

type param = string * Type.t
	[@@deriving eq, ord, show]
	
type t =
  | Var of string
  | Wildcard (* _ *)
  | App of t * t (* e1 e2 *)
  | Func of param * t (* fun (x:t) -> e *)
  | Ctor of string * t (* i(e) *)
  | Unctor of string * t (* i^-1(e) *)
  | Eq of bool * t * t (* e1 == e2 , e1 != e2 *)
  | Match of t * (Pattern.t * t) list (* match e with pat1 -> e1 | pat2 -> e2 | ... *)
  | Fix  of string * Type.t * t (* recursive function name, type, function body (Func of _) : let rec f:(t1 -> t2) = e *)
  | Tuple of t list (* (e1, e2, ..., en) *)
  | Proj of int * t (* e.g., (e1, e2)^-1 = e2*)
	[@@deriving eq, ord, show]

let var_str = "var"
let wildcard_str = "wildcard"
let app_str = "app"
let func_str = "func"
let ctor_str = "ctor"
let unctor_str = "unctor"
let eq_str = "eq"
let match_str = "match"
let fix_str = "fix"
let tuple_str = "tuple"
let proj_str = "proj"

let destruct_tuple e = 
	match e with 
	Tuple es -> es 
	| _ -> failwith "destruct_tuple: not a tuple"

let rec size_of_expr e =
	match e with
	| Var _ -> 1
  | Wildcard -> 1
  | App (e1, e2) -> (size_of_expr e1) + (size_of_expr e2)
  | Func (_, e') -> (size_of_expr e')
  | Ctor (_, e') -> (size_of_expr e') + 1
  | Unctor (_, e') -> (size_of_expr e')
  | Eq (_, e1, e2) -> (size_of_expr e1) + (size_of_expr e2) + 1
  | Match (e, patterns) -> 
		List.fold_left (fun acc (_, e') -> acc + (size_of_expr e') + 1) ((size_of_expr e) + 1) patterns
  | Fix (_, _, e') -> (size_of_expr e')
  | Tuple es -> List.fold_left (fun acc e' -> acc + (size_of_expr e')) 0 es 
  | Proj (_, e') -> (size_of_expr e')
		
let rec height_of_expr e =
	match e with
	| Var _ -> 1
	| Wildcard -> 1
	| App (e1, e2) -> (max (height_of_expr e1) (height_of_expr e2)) + 1
	| Func (_, e') -> (height_of_expr e') + 1
	| Ctor (_, e') -> (height_of_expr e') + 1
	| Unctor (_, e') -> (height_of_expr e') + 1
	| Eq (_, e1, e2) -> (max (height_of_expr e1) (height_of_expr e2)) + 1
	| Match (e', patterns) -> 
		(List.fold_left (fun acc (_, e') -> max acc (height_of_expr e')) (height_of_expr e') patterns) + 1
	| Fix (_, _, e') -> (height_of_expr e') + 1
	| Tuple es -> if BatList.is_empty es then 1 else BatList.max (List.map height_of_expr es)
	| Proj (_, e') -> (height_of_expr e') + 1

let rec match_depth e =
	match e with
	| Var _ -> 0
	| Wildcard -> 0
	| App (e1, e2) -> (max (match_depth e1) (match_depth e2))
	| Func (_, e') -> (match_depth e')
	| Ctor (_, e') -> (match_depth e')
	| Unctor (_, e') -> (match_depth e')
	| Eq (_, e1, e2) -> (max (match_depth e1) (match_depth e2))
	| Match (_, patterns) -> 
		(List.fold_left (fun acc (_, e') -> max acc (match_depth e')) 0 patterns) + 1
	| Fix (_, _, e') -> (match_depth e') + 1
	| Tuple es -> if BatList.is_empty es then 0 else BatList.max (List.map match_depth es)
	| Proj (_, e') -> (match_depth e')

let rec count_recursions e = 
	match e with 
	| Var i -> if String.equal i target_func then 1 else 0 
	| App (e1, e2) -> (count_recursions e1) + (count_recursions e2)
	| Func (_, e) -> (count_recursions e)
	| Ctor (_, e) -> (count_recursions e)
	| Unctor (_, e) -> (count_recursions e)
	| Eq (_, e1, e2) -> (count_recursions e1) + (count_recursions e2)
	| Match (e, patterns) -> 
		List.fold_left (fun acc (_, e) -> acc + (count_recursions e)) (count_recursions e) patterns 
	| Fix (_, _, e) -> (count_recursions e)
	| Tuple es -> List.fold_left (fun acc e -> acc + (count_recursions e)) 0 es
	| Proj (_, e) -> (count_recursions e) 
	| Wildcard -> 0


let rec cost_of_expr_with_input ?(in_list=[2.5;6.1;1.4;2.2;8.8;1.3;1.3;3.8;4.5;6.2;6.5;4.0]) e =
	match e with
	| Var _ -> (List.nth in_list 0)
	| Wildcard -> (List.nth in_list 1)
	| App (e1, e2) -> if (count_recursions e) < 1 then (cost_of_expr_with_input e1 ~in_list:in_list) +. (cost_of_expr_with_input e2 ~in_list:in_list) +. (List.nth in_list 2)
										else (cost_of_expr_with_input e1 ~in_list:in_list) +. (cost_of_expr_with_input e2 ~in_list:in_list) +. (List.nth in_list 3)
	| Func (_, e') -> (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 4)
	| Ctor (_, e') -> (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 5)
	| Unctor (_, e') -> (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 6)
	| Eq (_, e1, e2) -> (cost_of_expr_with_input e1 ~in_list:in_list) +. (cost_of_expr_with_input e2 ~in_list:in_list) +. (List.nth in_list 7)
	| Match (_, patterns) ->
		List.fold_left (fun acc (_, e') -> acc +. (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 8)) 0. patterns
	| Fix (_, _, e') -> (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 9)
	| Tuple es -> List.fold_left (fun acc e' -> acc +. (cost_of_expr_with_input e' ~in_list:in_list)) (List.nth in_list 10) es
	| Proj (_, e') -> (cost_of_expr_with_input e' ~in_list:in_list) +. (List.nth in_list 11)

(* score *)
let rec cost_of_expr e =
  match e with
  | Var _ -> 0
  | Wildcard -> 100
  | App (e1, e2) -> if (count_recursions e) < 1 then (cost_of_expr e1) + (cost_of_expr e2) + 2
										else (cost_of_expr e1) + (cost_of_expr e2) + 1
  | Func (_, e') -> (cost_of_expr e')
  | Ctor (_, e') -> (cost_of_expr e') + 1
  | Unctor (_, e') -> (cost_of_expr e')
  | Eq (_, e1, e2) -> (cost_of_expr e1) + (cost_of_expr e2) + 1
  | Match (e', patterns) ->
    List.fold_left (fun acc (_, e') -> acc + (cost_of_expr e') + 1) ((cost_of_expr e') + 1000) patterns
  | Fix (_, _, e') -> (cost_of_expr e')
  | Tuple es -> 
		if BatList.is_empty es then 10
		else 
			List.fold_left (fun acc e' -> acc + (cost_of_expr e')) 1 es
  | Proj (_, e') -> (cost_of_expr e')
			 
let ekind_of_expr expr = 
	match expr with 
	| Var i -> Var i
	| Wildcard -> Wildcard
	| App _ -> App (Wildcard, Wildcard)
	| Func (p, _) -> Func (p, Wildcard)
	| Ctor (i, _) -> Ctor (i, Wildcard)
	| Unctor (i, _) -> Unctor (i, Wildcard)
	| Eq (b, _, _) -> Eq (b, Wildcard, Wildcard)
	| Match (e', patterns) -> 
		let patterns' = List.map (fun (pat, _) -> (pat, Wildcard)) patterns in
		Match (e', patterns')
	| Fix (i, t, _) -> Fix (i, t, Wildcard)
	| Tuple _ -> Tuple []
	| Proj (i, _) -> Proj (i, Wildcard)	

let children_of_expr expr = 
	match expr with 
	| Var _ -> []
	| Wildcard -> []
	| App (e1, e2) -> [e1; e2]
	| Func (_, e') -> [e']
	| Ctor (_, e') -> [e']
	| Unctor (_, e') -> [e']
	| Eq (_, e1, e2) -> [e1; e2]
	| Match (_, patterns) -> 
		(List.map (fun (_, e) -> e) patterns)
	| Fix (_, _, e') -> [e']
	| Tuple es -> es
	| Proj (_, e') -> [e']
	

let rec get_expr_from_addr expr addr = 
	if BatList.is_empty addr then expr 
	else 
		let expr' = 
			match expr with 
			| Func (_, e) -> BatList.at [Wildcard; e] (BatList.hd addr)
			| Ctor (_, e) -> BatList.at [Wildcard; e] (BatList.hd addr)
			| Unctor (_, e) -> BatList.at [Wildcard; e] (BatList.hd addr)
			| Eq (_, e1, e2) -> BatList.at [Wildcard; e1; e2] (BatList.hd addr)
			| Match (e, patterns) -> 
				let es = List.map (fun (_, e) -> e) patterns in
				BatList.at (e :: es) (BatList.hd addr)
			| Fix (_, _, e) -> BatList.at [Wildcard; Wildcard; e] (BatList.hd addr)
			| Tuple es -> BatList.at es (BatList.hd addr)
			| Proj (_, e) -> BatList.at [Wildcard; e] (BatList.hd addr)
			| App (e1, e2) -> BatList.at [e1; e2] (BatList.hd addr)
			| _ -> 
				failwith (Printf.sprintf "get_expr_from_addr: expr %s at addr %s" (show expr) (string_of_list string_of_int addr))
		in
		get_expr_from_addr expr' (BatList.tl addr)


let construct_from_ekind_and_argexprs ekind es =
	match ekind with 
	| Var _ | Wildcard -> ekind
		(* let _ = assert ((List.length es) = 1) in
		List.hd es *)
	| App _ -> 
		let _ = assert ((List.length es) = 2) in
		App (List.nth es 0, List.nth es 1) 	
	| Func (p, _) -> 
		let _ = assert ((List.length es) = 1) in
		Func (p, List.hd es)
	| Ctor (i, _) -> 
		let _ = assert ((List.length es) = 1) in
		Ctor (i, List.hd es)
	| Unctor (i, _) -> 
		let _ = assert ((List.length es) = 1) in
		Unctor (i, List.hd es)	
	| Eq (b, _, _) -> 
		let _ = assert ((List.length es) = 2) in
		Eq (b, List.nth es 0, List.nth es 1)
	| Match (e, patterns) ->
		(* let _ = assert ((List.length es) = (List.length patterns) + 1) in *)
		(* Match (List.hd es, List.map2 (fun (pat, _) e' -> (pat, e')) patterns (List.tl es))   	 *)
		Match (e, List.map2 (fun (pat, _) e' -> (pat, e')) patterns es)   	
	| Fix (i, t, _) -> 
		let _ = assert ((List.length es) = 1) in
		Fix (i, t, List.hd es)
	| Tuple _ -> Tuple es 
	| Proj (i, _) ->
		let _ = assert ((List.length es) = 1) in
		Proj (i, List.hd es) 
	 
let rec show ?(indent=0) e =
	let make_indent indent = 
		(BatString.make (indent*2) ' ')
	in 
	let result = 
  	match e with 
  	| Var i -> i 
  	| Wildcard -> "_"
  	| App (e1, e2) -> Printf.sprintf "(%s %s)" (show e1) (show e2)
  	| Func ((p,t), e') -> 
  		Printf.sprintf "fun (%s:%s) -> \n%s" p (Type.show t) (show ~indent:(indent+1) e')
  	| Ctor (i, e') -> Printf.sprintf "%s(%s)" i (show e')
  	| Unctor (i, e') -> Printf.sprintf "Un_%s(%s)" i (show e')
  	| Eq (b, e1, e2) -> 
			Printf.sprintf "%s %s %s" (show e1) (if b then "=" else "<>") (show e2)
  	| Match (e', patterns) -> 
  		Printf.sprintf "match %s with\n%s%s" (show e') (make_indent indent)  
				(List.fold_left (fun acc (p, e') -> 
					acc ^ (Printf.sprintf "%s -> \n%s\n%s" (Pattern.show p) (show ~indent:(indent+1) e') (make_indent indent) )
				 ) "" patterns)
		| Fix (i, t, e') -> 
			Printf.sprintf "let rec (%s : %s) = \n%s" i (Type.show t) (show ~indent:(indent + 1) e')
		| Tuple es -> 
			string_of_list ~first:"[" ~last:"]" ~sep:", " (fun e -> show ~indent:0 e) es 
		| Proj (i, e') -> 
			Printf.sprintf "(%s).%d" (show e') i   	   
	in
	(make_indent indent) ^ result 

type value = 
  | FuncV of param * t
  | CtorV of string * value
  | TupleV of value list
  | WildcardV
	| Bot
	[@@deriving eq, show]
	
let is_func_value v = 
	match v with FuncV _ -> true | _ -> false

let is_ctor_value v = 
	match v with CtorV _ -> true | _ -> false

let is_tuple_value v = 
	match v with TupleV _ -> true | _ -> false

let is_wildcard_value v = 
	match v with WildcardV -> true | _ -> false

let is_bot_value v = 
	match v with Bot -> true | _ -> false
				
let rec exp_of_value (v:value) : t = 
	match v with 
	| FuncV (p, e) -> Func (p, e)
  | CtorV (i, v') -> Ctor(i, exp_of_value v')
	| WildcardV -> Wildcard
	| TupleV vs -> Tuple (List.map exp_of_value vs)
	| Bot -> failwith "invalid input: exp_of_value"

let show_value v = 
	match v with 
	| Bot -> "bot"
	| _ -> show (exp_of_value v) 
	 
(* for checking structural recursiveness *)	
let rec leq_value v1 v2 = 
	let result = 
  	if equal_value v1 v2 then true 
  	else 
    	match v1, v2 with 
  		(* do not permit comparisons between funcs *)
  		(* (because we compare values only for checking structrual recursiveness) *)
  		| FuncV(_), _ -> false
  		| _, FuncV(_) -> false
    	| _, WildcardV -> true
    	| Bot, _ -> true
  		| TupleV vs, _ when BatList.is_empty vs -> true
    	| CtorV (_), CtorV(_, v2') ->
    		leq_value v1 v2'
			| CtorV _, TupleV v2s ->
    		List.exists (leq_value v1) v2s
			| TupleV v1s, CtorV(_) ->
				if (List.length v1s) = 1 then
					leq_value (List.hd v1s) v2
				else false 
  		| TupleV v1s, TupleV v2s ->
  			if (List.length v1s) > (List.length v2s) then false
  			else
    			List.for_all (fun v1 -> List.exists (leq_value v1) v2s) v1s
  		| _ -> false  
	in
	result 
		
let lt_value v1 v2 = 
	(leq_value v1 v2) && (not (equal_value v1 v2))
	 
	
type declaration =
  | TypeDeclaration of string * Type.t
  | ExprDeclaration of string * t
	[@@deriving eq, show]


let unit_ = (Tuple [])
let true_ = (Ctor ("True",unit_))
let false_ = (Ctor ("False",unit_))

let unitv_ = (TupleV [])
let truev_ = (CtorV ("True",unitv_))
let falsev_ = (CtorV ("False",unitv_))
	
let is_bot v = match v with Bot -> true | _ -> false 

let rec from_int n =
  if n = 0 then
    (Ctor ("O", unit_))
  else
    (Ctor ("S", from_int (n-1)))
		
let is_var_exp t = 
	match t with 
	Var _ -> true 
	| _ -> false

let is_wildcard_exp t = 
	match t with  
  | Wildcard -> true
	| _ -> false 

let is_app_exp t = 
	match t with 
  | App _ -> true 
	| _ -> false 

let is_func_exp t =
	match t with 
  | Func _ -> true 
	| _ -> false 

let is_ctor_exp t =
	match t with 
  | Ctor _ -> true
	| _ -> false 

let is_unctor_exp t =
	match t with 
  | Unctor _ -> true
	| _ -> false 

let is_eq_exp t =
	match t with 
  | Eq _ -> true 
	| _ -> false 
	
let is_match_exp t =
	match t with 
  | Match _ -> true 
	| _ -> false 

let is_fix_exp t =
	match t with 
  | Fix  _ -> true
	| _ -> false 

let is_tuple_exp t =  
	match t with 
  | Tuple _ -> true 
	| _ -> false 

let is_proj_exp t =
	match t with 
  | Proj _ -> true 
	| _ -> false 
	
let rec contains_id i e =
	match e with 
	| Var i' -> String.equal i i'  
  | App (e1, e2) -> (contains_id i e1) || (contains_id i e2)
  | Func (_, e) -> (contains_id i e)
  | Ctor (_, e) -> (contains_id i e)
  | Unctor (_, e) -> (contains_id i e)
  | Eq (_, e1, e2) -> (contains_id i e1) || (contains_id i e2)
  | Match (_, patterns) -> 
		List.fold_left (fun acc (_, e) -> acc || (contains_id i e)) false patterns 
  | Fix (i', _, e) -> (String.equal i i') || (contains_id i e)
  | Tuple es -> 
		(not (BatList.is_empty es)) && (List.for_all (contains_id i) es) 
  | Proj (_, e) -> (contains_id i e) 
	| _ -> false  
	
(* collect all sub-expressions of e which could be referred as a variable in pattern matching *)
(* v -> x | v.i | Unctor(c,v) *)
let rec get_pattern_match_vars e =
	match e with 
	| Var i -> 
		if String.equal i target_func_arg then BatSet.singleton e
		else BatSet.empty     
  | App (e1, e2) -> BatSet.union (get_pattern_match_vars e1) (get_pattern_match_vars e2)
  | Func (_, e') -> (get_pattern_match_vars e')
  | Ctor (_, e') -> (get_pattern_match_vars e')
  | Unctor (_, e') ->
		if contains_id target_func_arg e then   
			BatSet.add e (get_pattern_match_vars e')
		else (get_pattern_match_vars e')
  | Eq (_, e1, e2) -> BatSet.union (get_pattern_match_vars e1) (get_pattern_match_vars e2)
  | Match (e', patterns) -> 
		List.fold_left (fun acc (_, e') -> 
			BatSet.union acc (get_pattern_match_vars e')
		) (get_pattern_match_vars e') patterns 
  | Fix (_, _, e') -> get_pattern_match_vars e'
  | Tuple es -> 
		List.fold_left (fun acc e' -> 
			BatSet.union acc (get_pattern_match_vars e')
		) BatSet.empty es
  | Proj (_, e') -> 
		if contains_id target_func_arg e then   
			BatSet.add e (get_pattern_match_vars e')
		else (get_pattern_match_vars e') 
	| _ -> BatSet.empty   
	

let is_recursive e = 
	(count_recursions e) > 0 

let rec get_scrutinees e = 
	match e with 
	| Match(scrutinee, patterns) -> 
		BatSet.add scrutinee (List.fold_left (fun acc (_, e') -> 
			BatSet.union acc (get_scrutinees e')
		) BatSet.empty patterns)
	| _ -> BatSet.empty

let rec get_recursive_calls e = 
	match e with 
  | App (Var i, _) when (BatString.equal i target_func) ->
		BatSet.singleton e 
	| App (e1, e2) -> 
		BatSet.union (get_recursive_calls e1) (get_recursive_calls e2)  
  | Func (_, e) -> get_recursive_calls e
  | Ctor (_, e) -> get_recursive_calls e
  | Unctor (_, e) -> get_recursive_calls e
  | Eq (_, e1, e2) -> BatSet.union (get_recursive_calls e1) (get_recursive_calls e2)
  | Match (e, patterns) -> 
		List.fold_left (fun acc (_, e) -> BatSet.union acc (get_recursive_calls e)) (get_recursive_calls e) patterns 
  | Fix (_, _, e) -> (get_recursive_calls e)
  | Tuple es -> List.fold_left (fun acc e -> BatSet.union acc (get_recursive_calls e)) BatSet.empty es
  | Proj (_, e) -> (get_recursive_calls e)
	| _ -> BatSet.empty  

let rec get_constructors e = 
	match e with 
  | App (e1, e2) -> BatSet.union (get_constructors e1) (get_constructors e2) 
  | Func (_, e) -> get_constructors e
  | Ctor (_, e') -> BatSet.add e (get_constructors e')
  | Unctor (_, e) -> get_constructors e
  | Eq (_, e1, e2) -> BatSet.union (get_constructors e1) (get_constructors e2)
  | Match (_, patterns) -> 
		List.fold_left (fun acc (_, e) -> BatSet.union acc (get_constructors e)) BatSet.empty patterns 
  | Fix (_, _, e) -> (get_constructors e)
  | Tuple es -> List.fold_left (fun acc e -> BatSet.union acc (get_constructors e)) BatSet.empty es
  | Proj (_, e) -> (get_constructors e)
	| _ -> BatSet.empty  

let rec get_unconstructors e = 
	match e with 
  | App (e1, e2) -> BatSet.union (get_unconstructors e1) (get_unconstructors e2) 
  | Func (_, e) -> get_unconstructors e
  | Ctor (_, e) -> get_unconstructors e
  | Unctor (_, e') -> BatSet.add e (get_unconstructors e')
  | Eq (_, e1, e2) -> BatSet.union (get_unconstructors e1) (get_unconstructors e2)
  | Match (_, patterns) -> 
		List.fold_left (fun acc (_, e) -> BatSet.union acc (get_unconstructors e)) BatSet.empty patterns 
  | Fix (_, _, e) -> (get_unconstructors e)
  | Tuple es -> List.fold_left (fun acc e -> BatSet.union acc (get_unconstructors e)) BatSet.empty es
  | Proj (_, e) -> (get_unconstructors e)
	| _ -> BatSet.empty  
	
let using_allowed_unconstructor expr available_uncons = 
	(BatSet.subset (get_unconstructors expr) available_uncons)

let rec get_args e =
	match e with 
 	| App (Var _, e2) -> (get_args e2)
	| App (e1, e2) -> BatSet.union (get_args e1) (get_args e2)
	| Func (_, e) -> get_args e
  | Ctor (_, e) -> get_args e
  | Unctor (_, e) -> get_args e
  | Eq (_, e1, e2) -> BatSet.union (get_args e1) (get_args e2)
  | Match (e, patterns) -> 
		List.fold_left (fun acc (_, e) -> BatSet.union acc (get_args e)) (get_args e) patterns 
  | Fix (_, _, e) -> (get_args e)
  | Tuple es -> List.fold_left (fun acc e -> BatSet.union acc (get_args e)) BatSet.empty es
  | Proj (_, e) -> (get_args e)
	| _ -> BatSet.singleton e
		

(* true if e is an argument expression of the target function that should be decreased *)	
let rec is_decreasing_expr ?(idx=None) e = 
	match e with 
	| Unctor(_, Var i) when BatString.equal i target_func_arg -> true
	| Unctor(_, Proj(n, Var i)) when BatString.equal i target_func_arg -> 
		BatOption.is_none idx || (BatOption.get idx) = n
	| Proj(_, e') -> is_decreasing_expr ~idx:idx e'
	| Unctor(_, e') -> is_decreasing_expr ~idx:idx e'
	| Tuple es -> List.exists (is_decreasing_expr ~idx:idx) es
	| _ -> false

(* get indices of arguments that should be decreased to guarantee termination *)	
let rec get_keyargs e = 
	let rec get_idxs e = 
		match e with 
		| Proj(n, Var i) when BatString.equal i target_func_arg -> BatSet.singleton n
		| Proj(_, e') -> get_idxs e'
		| Unctor(_, e') -> get_idxs e'
		| Tuple es -> List.fold_left (fun acc e -> BatSet.union acc (get_idxs e)) BatSet.empty es
		| App (e1, e2) -> BatSet.union (get_idxs e1) (get_idxs e2)
		| Func (_, e) -> get_idxs e
		| Ctor (_, e) -> get_idxs e
		| Eq (_, e1, e2) -> BatSet.union (get_idxs e1) (get_idxs e2)
		| _ -> BatSet.empty
	in 
	match e with 
	| Match(e, patterns) -> 
		let idxs = get_idxs e in 
		List.fold_left (fun acc (_, branch) -> 
			match branch with 
			| Match _ -> BatSet.union acc (get_keyargs branch) 
			| _ -> 
				let rec_exprs_in_branch = 
					get_recursive_calls branch 
				in 
				if BatSet.is_empty rec_exprs_in_branch then 
					BatSet.union idxs acc 
				else acc 
		) BatSet.empty patterns
	| _ -> BatSet.empty	
	
let value_of_bool b = 
	if b then truev_ else falsev_

(* constructor / destructor simplification (Section 5.4)*)
let rec normalize e =
	match e with 
	| Ctor (i1, Unctor (i2, e')) -> 
		if (String.equal i1 i2) then normalize e' 
		else Ctor (i1, Unctor (i2, normalize e'))
	| Unctor (i1, Ctor (i2, e')) ->
		if (String.equal i1 i2) then normalize e' 
		else Unctor (i1, Ctor (i2, normalize e'))
	| App (e1, e2) -> App (normalize e1, normalize e2)
	| Func (p, e') -> Func (p, normalize e')
	| Eq (b, e1, e2) -> Eq (b, normalize e1, normalize e2)
	| Match (e', pats) -> 
		Match (normalize e', List.map (fun (pat, e) -> (pat, normalize e)) pats)
	| Fix (i, t, e') -> Fix (i, t, normalize e')
	| Tuple es -> Tuple (List.map normalize es)
	| Proj (i, e') -> Proj (i, normalize e')
	| _ -> e  	 
	
let rec replace (i:string) (e_with:t) (e:t) : t =
  let replace_simple = replace i e_with in
  begin 
 	match e with
   | Wildcard -> e
   | Eq (b,e1,e2) ->
     Eq (b, (replace_simple e1), (replace_simple e2))
   | Var i' ->
     if String.equal i i' then e_with
     else e
   | App (e1,e2) ->
     App ((replace_simple e1), (replace_simple e2))
   | Func ((i',t),e') ->
     if String.equal i i' then e
     else Func ((i',t), (replace_simple e'))
   | Ctor (i,e) ->
     Ctor (i, (replace_simple e))
   | Unctor (i,e) ->
     Unctor (i, (replace_simple e))
   | Match (e,branches) ->
     let branches =
       List.map (fun (p,e) ->
         if Pattern.contains_id i p then (p,e) (* ?? *)
         else (p, replace_simple e)
 			) branches
     in
     Match ((replace_simple e), branches)
   | Fix (i',t,e') ->
     if String.equal i i' then e
     else Fix (i', t, (replace_simple e'))
   | Tuple es ->
     Tuple (List.map replace_simple es)
   | Proj (i,e) ->
     Proj (i, (replace_simple e))
  end

let replace_holes eval_context (e:t) : t =
  BatMap.foldi (fun i e acc -> replace i e acc) eval_context e  

let rec replace_expr (e_src:t) (e_dst:t) (e:t) : t =
	let result = 
		if (equal e e_src) then e_dst 
		else 
		let replace_simple = replace_expr e_src e_dst in
		begin 
			match e with
			| Eq (b,e1,e2) ->
				Eq (b, (replace_simple e1), (replace_simple e2))
			| App (e1,e2) ->
				App ((replace_simple e1), (replace_simple e2))
			| Func ((i',t),e') ->
				Func ((i',t), (replace_simple e'))
			| Ctor (i,e) ->
				Ctor (i, (replace_simple e))
			| Unctor (i,e) ->
				Unctor (i, (replace_simple e))
			| Match (e,branches) ->
				let branches =
					List.map (fun (p,e) -> (p, replace_simple e)) branches
				in
				Match ((replace_simple e), branches)
			| Fix (i',t,e') ->
				Fix (i', t, (replace_simple e'))
			| Tuple es ->
				Tuple (List.map replace_simple es)
			| Proj (i,e) ->
				Proj (i, (replace_simple e))
			| _ -> e
		end
	in
	result

let rec matches_pattern_and_extractions (p:Pattern.t) (v:value)
  : (string * value) list =
  begin 
		match (p, v) with
    | (Pattern.Tuple ps, TupleV vs) ->
      List.map2 matches_pattern_and_extractions ps vs |> List.concat
    | (Pattern.Ctor (i,p),CtorV (i',v)) ->
      if String.equal i i' then
        matches_pattern_and_extractions p v
      else raise InvalidPatternMatch
    | (Pattern.Var i,_) ->
			let _ = assert (v <> WildcardV) in  
			[(i,v)]
    | (Pattern.Wildcard,_) -> []
    | _ -> failwith ("bad typechecking: pattern: " ^ Pattern.show p ^ "value: " ^ show_value v)
  end

type node = t * int list [@@deriving show](* (exprkind, children) *)
type value_or_exn = Value of value | Exn of string 	[@@deriving show]

let nid = ref 0;;
let id2node = ref BatMap.empty (* (int, node) BatMap.t  *)
let node2id = ref BatMap.empty (* (node, int) BatMap.t  *)
let id2v = ref BatMap.empty;; (* (int, value_or_exn) BatMap.t *)

let id_of_node node = 
	if BatMap.mem node !node2id then 
		BatMap.find node !node2id
	else 
		let _ = nid := !nid + 1 in 
		let _ = id2node := BatMap.add !nid node !id2node in
		let _ = node2id := BatMap.add node !nid !node2id in
		!nid

let rec node_of_expr (e : t) : (int * node) = 
	let ekind = ekind_of_expr e in 
	(* match e with 
	| Var _  | Wildcard -> 
		let node = (ekind, []) in 
		let id = id_of_node node in 
		(id, node)
	| _ -> *)
		let children_nodes = List.map (fun e' -> fst (node_of_expr e')) (children_of_expr e) in
		let node = (ekind, children_nodes) in
		let id = id_of_node node in
		(id, node)

let rec expr_of_node (ekind, ids) = 
	match ekind with 
	| Var _ | Wildcard -> ekind
	| _ -> 
		let children = List.map (fun id -> expr_of_node (BatMap.find id !id2node)) ids in
		construct_from_ekind_and_argexprs ekind children

(* let cache = Hashtbl.create ~random:false 100000 *)
let eval_time = ref 0. 
let rec evaluate (e : t) : value =
	(* if (Hashtbl.mem cache e) then Hashtbl.find cache e
	else *)
	let result = 
    match e with
    | Wildcard -> WildcardV
    | Var i -> failwith ("unbound variable " ^ i)
  	| App (e1, e2) ->
      let v1 = evaluate e1 in
      (* let e1 = exp_of_value v1 in *)
      begin 
  			match v1 with
        | FuncV ((i,_),e1) ->
          let v2 = evaluate e2 in
          let e2 = exp_of_value v2 in 
  				evaluate (replace i e2 e1) 
        | WildcardV -> WildcardV
        | _ -> failwith "nonfunc applied"
      end
    | Eq (b,e1,e2) ->
      let v1 = evaluate e1 in
      let v2 = evaluate e2 in
      let eq = equal_value v1 v2 in
      let res = if b then eq else not eq in
      value_of_bool res
    | Func (a,e) -> FuncV(a, e)
    | Ctor (i,e) ->
      let v = evaluate e in
      CtorV (i, v)
    | Match (e,branches) as match_expr ->
      let v = evaluate e in
      let bindings_branchexp_opt : ((string * value) list * t) option list =
  			List.map (fun (p,branch_e) ->
  				try 
  					Some ((matches_pattern_and_extractions p v), branch_e)
  				with InvalidPatternMatch -> None  
  			) branches
      in
      let (bindings,branch_e) =
  			if List.for_all (BatOption.is_none) bindings_branchexp_opt then
  				 failwith ((show_value v) ^ " not matched: \n " ^ (show match_expr))
  			else 
  				List.find BatOption.is_some bindings_branchexp_opt |> BatOption.get
      in
  		let eval_context = 
  			List.fold_left (fun ec (i,v) ->
					let _ = assert (v <> WildcardV) in  
  				BatMap.add i (exp_of_value v) ec
  			) BatMap.empty bindings 
			in 
  		evaluate (replace_holes eval_context branch_e)
    | Fix (i,_,e') ->
  		evaluate (replace i e e')
    | Tuple es ->
      let vs = List.map evaluate es in
      TupleV vs
    | Proj (i,e) ->
      let v = evaluate e in
      begin 
  			match v with
        | WildcardV -> WildcardV
        | TupleV vs -> List.nth vs i
        | _ -> failwith "bad projection!"
      end
    | Unctor (i,e) ->
      let v = evaluate e in
  		begin 
  			match v with
  			| CtorV(i', v') ->
  				if (String.equal i  i') then v' else failwith "bad unconstructor!"
  			| _ -> failwith "bad unconstructor!"
    	end
	in
	(* let _ = Hashtbl.add cache e result in *)
	result

let rec evaluate_node (((ekind, ids) as n) : node) : value =
	(* let _ = print_endline ("evaluating node: " ^ (show_node n)) in  *)
	let id = BatMap.find n !node2id in 
	if (BatMap.mem id !id2v) then 
		match BatMap.find id !id2v with 
		| Value v -> v
		| Exn s -> failwith s
	else
	try
	let result = 
		match ekind with
		| Wildcard -> WildcardV
		| Var i -> failwith ("unbound variable " ^ i)
		| App _ ->
			let _ = assert ((List.length ids) = 2) in
			let v1 = BatMap.find (List.nth ids 0) !id2node |> evaluate_node in
			begin 
				match v1 with
				| FuncV ((i,_),e1) ->
					let v2 = BatMap.find (List.nth ids 1) !id2node |> evaluate_node in
					let e2 = exp_of_value v2 in 
					(* evaluate (replace i e2 e1) *)
					evaluate_node (snd (node_of_expr (replace i e2 e1)))
				| WildcardV -> WildcardV
				| _ -> failwith "nonfunc applied"
			end
		| Eq _ ->
			let _ = assert ((List.length ids) = 2) in
			let v1 = BatMap.find (List.nth ids 0) !id2node |> evaluate_node in
			let v2 = BatMap.find (List.nth ids 1) !id2node |> evaluate_node in
			let eq = equal_value v1 v2 in
			let res = if eq then eq else not eq in
			value_of_bool res
		| Func (a,_) -> 
			let _ = assert ((List.length ids) = 1) in
			FuncV(a, BatMap.find (List.nth ids 0) !id2node |> expr_of_node)
		| Ctor (i,_) ->
			let _ = assert ((List.length ids) = 1) in
			let v = BatMap.find (List.nth ids 0) !id2node |> evaluate_node in
			CtorV (i, v)
		| Match (e,branches) as match_expr ->
			let v = evaluate e in
			let bindings_branchexp_opt : ((string * value) list * node) option list =
				List.mapi (fun i (p,_) ->
					try 
						let n = BatMap.find (List.nth ids i) !id2node in 
						Some ((matches_pattern_and_extractions p v), n)
					with InvalidPatternMatch -> None  
				) branches
			in
			let (bindings,branch_e) =
				if List.for_all (BatOption.is_none) bindings_branchexp_opt then
						failwith ((show_value v) ^ " not matched: \n " ^ (show match_expr))
				else 
					List.find BatOption.is_some bindings_branchexp_opt |> BatOption.get
			in
			let eval_context = 
				List.fold_left (fun ec (i,v) ->
					let _ = assert (v <> WildcardV) in  
					BatMap.add i (exp_of_value v) ec
				) BatMap.empty bindings 
			in 
			let branch_e = expr_of_node branch_e in 
			(replace_holes eval_context branch_e) |> node_of_expr |> snd  |> evaluate_node 
		| Fix (i,_,_) ->
			let _ = assert ((List.length ids) = 1) in
			let e = expr_of_node n in 
			(* let _ = print_endline ("fix: " ^ (show e)) in *)
			let n' = BatMap.find (List.nth ids 0) !id2node in 
			let e' = expr_of_node n' in
			(* let _ = print_endline ("body: " ^ (show e')) in *)
			(* evaluate (replace i e e') *)
			evaluate_node (snd (node_of_expr (replace i e e')))
		| Tuple _ ->
			let ns = List.map (fun id -> BatMap.find id !id2node) ids in
			let vs = List.map evaluate_node ns in
			TupleV vs
		| Proj (i,_) ->
			let _ = assert ((List.length ids) = 1) in
			let v = BatMap.find (List.nth ids 0) !id2node |> evaluate_node in
			begin 
				match v with
				| WildcardV -> WildcardV
				| TupleV vs -> List.nth vs i
				| _ -> failwith "bad projection!"
			end
		| Unctor (i,_) ->
			let _ = assert ((List.length ids) = 1) in
			let v = BatMap.find (List.nth ids 0) !id2node |> evaluate_node in
			begin 
				match v with
				| CtorV(i', v') ->
					if (String.equal i  i') then v' else failwith "bad unconstructor!"
				| _ -> failwith "bad unconstructor!"
			end
	in
	let _ = id2v := BatMap.add (BatMap.find n !node2id) (Value result) !id2v in
	result
	with Failure s -> 
		let _ = id2v := BatMap.add (BatMap.find n !node2id) (Exn s) !id2v in
		failwith s		

(* let evaluate e = 
	let n = snd (node_of_expr e) in
	(* let _ = print_endline ("before evaluation of " ^ (show e)) in
	let _ = print_endline ("id2node : " ^ (string_of_map string_of_int show_node !id2node)) in
	let _ = print_endline ("id2v : " ^ (string_of_map string_of_int show_value_or_exn !id2v)) in
	let _ = print_endline ("node : " ^ (show_node n)) in *)
	let result = evaluate_node n in 
	(* let _ = print_endline ("after evaluation of " ^ (show e)) in
	let _ = print_endline ("id2node : " ^ (string_of_map string_of_int show_node !id2node)) in
	let _ = print_endline ("id2v : " ^ (string_of_map string_of_int show_value_or_exn !id2v)) in
	let _ = print_endline ("node : " ^ (show_node n)) in *)
	result *)
	
		
let evaluate_with_context eval_context (e : t) : value =
	let e = replace_holes eval_context e in
  evaluate e

let safe_evaluate (e : t) : value =
	try
  	evaluate e 
	with Failure _ -> Bot

let safe_evaluate_with_context eval_context (e : t) : value =
	try
		let e = replace_holes eval_context e in
  	evaluate e 
	with Failure _ -> 
		Bot
	
