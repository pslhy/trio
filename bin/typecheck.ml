open Expr
open Type
open Vocab

let rec concretify td t = 
  match t with
  | Named i ->
    (try
			concretify td (BatMap.find i td)
		with _ -> t)
  | _ -> t

(* return : (string * t) list *)
let rec typecheck_pattern td (p:Pattern.t) t =
  match (p, (concretify td t)) with
  | (Tuple ps, Tuple ts) ->
    let merges =
      List.map2 (typecheck_pattern td) ps ts
    in
    List.concat merges
  | (Ctor (i,p), Variant variants) ->
    let t = List.assoc i variants in
    typecheck_pattern td p t
	| (Ctor (i,p), Named i') ->
    let t = 
			try 
				begin 
  				match (BatMap.find i' td) with 
  				| Variant variants -> List.assoc i variants 
  				| _ ->  failwith ("typecheck_pattern: " ^ i')
				end
			with _ -> 
				let _ = prerr_endline (string_of_map id Type.show td) in  
				failwith ("typecheck_pattern: " ^ i') 
		in
    typecheck_pattern td p t
  | (Var i,_) -> [(i,t)]
  | (Wildcard,_) -> []
  | _ -> failwith ("didn't merge " ^ (Pattern.show p) ^ " with " ^ (Type.show t))
  

type eval_context = (string, Expr.t) BatMap.t
type type_context = (string, Type.t) BatMap.t
type type_definition = (string, Type.t) BatMap.t
type variant_context = (string, Type.t * Type.t) BatMap.t (* arg_ty * parent_ty *)

let rec typecheck_exp (ec:eval_context) (tc:type_context) 
											(td:type_definition) (vc:variant_context) (e:Expr.t) : Type.t =
  let typecheck_simple = typecheck_exp ec tc td vc in
  (* let _ = my_prerr_endline ("type check: " ^ (Expr.show e)) in *)
  match e with
  | Wildcard -> failwith ("not typeable: " ^ (Expr.show e))
  | Unctor (i, _) ->
		begin
		 try fst (BatMap.find i vc)   
		 with _ -> failwith "typecheck error: unctor"
		end
  | Var v ->
		(try BatMap.find v tc with _ -> failwith ("variable " ^ v ^ " not found"))
  | Eq (_,e1,e2) ->
    let _ = typecheck_simple e1 in
    let _ = typecheck_simple e2 in
    (* assert (type_equiv tc t1 t2); *)
    _bool
  | App (e1,e2) ->
    let t1 = concretify td (typecheck_simple e1) in
    let (_,t12) = try destruct_arrow t1 with _ -> failwith ("destruct_arrow: " ^ Type.show t1) in
    let _ = typecheck_simple e2 in
    (* if type_equiv tc t11 t2 then *)
      t12
    (* else                                 *)
    (*   failwith ("applied invalid type: " *)
    (*             ^ (show_t t2)         *)
    (*             ^ " instead of "         *)
    (*             ^ (show_t t11))       *)
  | Func ((i,t),e) ->
    let tc' = BatMap.add i t tc in
    Arrow (t, (typecheck_exp ec tc' td vc e))
  | Ctor (i,e) ->
    let _ = typecheck_simple e in
    let _, parent_ty = try BatMap.find i vc with _ -> failwith "typecheck: ctor" in
    (* if type_equiv tc arg_ty t then *)
			(* Variant [(i, arg_ty)] *)
      parent_ty
    (* else                                                                        *)
    (*   failwith ("variant " ^ (Id.show i) ^ " expects different type: expected " *)
    (*             ^ (show_t t_defined) ^ " but got " ^ (show_t t))          *)
  | Match(e,branches) ->
    let t = concretify td (typecheck_simple e) in
    let ts =
      List.map (fun (p,e) ->
        let its = typecheck_pattern td p t in
        let tc = map_add_multiple its tc in
        typecheck_exp ec tc td vc e
			) branches
    in
    let (ht,_) = (List.hd ts, List.tl) in
    (* assert (List.for_all ~f:(fun t -> type_equiv tc ht t) tt); *)
    ht
  | Fix (i,t,e) ->
    let tc' = BatMap.add i t tc in
    typecheck_exp ec tc' td vc e
  | Tuple es -> Tuple (List.map typecheck_simple es)
  | Proj (i,e) ->
    let t = concretify td (typecheck_simple e) in
    let ts = destruct_tuple t in
    List.nth ts i
