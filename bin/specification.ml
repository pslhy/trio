open Expr

type unprocessed_spec =
  | UIOEs of (Expr.t list * Expr.t) list (* list of inputs and output*)
[@@deriving show]

type spec = (value * value) list (* list of inputs (in a tuple) and output *)
[@@deriving show]

type t_unprocessed = string list (* import file list *)
                     * declaration list (* type and value declarations *)
                     * Type.t (* type of a target function to be synthesized *)
                     * unprocessed_spec (* behavioral constraint *)
[@@deriving show]


type eval_context = Typecheck.eval_context
type type_context = Typecheck.type_context
type type_definition = Typecheck.type_definition
type variant_context = Typecheck.variant_context
(* type eval_context = (string, Expr.t) BatMap.t                                      *)
(* type type_context = (string, Type.t) BatMap.t                                      *)
(* type type_definition = (string, Type.t) BatMap.t                                   *)
(* type variant_context = (string, Type.t * Type.t) BatMap.t (* arg_ty * parent_ty *) *)

type t = {
  synth_type   : Type.t * Type.t;  (* types of inputs (in a tuple) and output *)
  ec           : eval_context; (* evaluation context : variable -> definition (expression) *)
  tc           : type_context; (* type context : variable -> type *)
	td           : type_definition; (* type definitions : name -> type *)
  vc           : variant_context; (* variants context : constructor name -> argument type * parent type *)
  spec         : (value * value) list ; (* inputs (in a tuple) and output *)
}

let show t = 
	let id x = x in 
	Printf.sprintf "synth_type: %s -> %s\n ec: %s\n tc: %s\n td: %s\n vc: %s\n spec: %s\n"
		(Type.show (fst t.synth_type)) (Type.show (snd t.synth_type))
		(Vocab.string_of_map id Expr.show t.ec)
		(Vocab.string_of_map id Type.show t.tc)
		(Vocab.string_of_map id Type.show t.td)
		(Vocab.string_of_map id (fun (ty1,ty2) -> (Type.show ty1) ^ ", " ^ (Type.show ty2)) t.vc)
		(Vocab.string_of_list (fun (i,o) -> (show_value i) ^ ", " ^ (show_value o)) t.spec)	
		
(* types are given right-associative *)
(* (ty1 -> (ty2 -> ... -> tyn))   =>   (ty1, ..., tyn-1), tyn    *)
let st_to_pair (synth_type:Type.t) : Type.t * Type.t =
	let rec f (acc, t) = 
		match t with 
		| Type.Arrow (t1, t2) -> f (t1::acc, t2) 
		| _ -> (List.rev acc, t) 
	in
	let ts, t = f ([], synth_type) in
	if (List.length ts) = 1 then 
		(List.hd ts, t)
	else   
		(Type.Tuple ts, t)
	

let rec extract_variants (t:Type.t)
    : (string * Type.t) list =
		match t with 
		| Named _ -> [] 
    | Arrow (t1, t2) -> (extract_variants t1) @ (extract_variants t2)
    | Tuple tys -> List.fold_left (fun vs ty -> vs @ (extract_variants ty)) [] tys  
    | Variant vs -> 
			List.fold_left (fun vs (_, ty) -> vs @ (extract_variants ty)) vs vs
			(* vs *)
			  
		
let process_decl_list (decls:declaration list) 
			: (eval_context * type_context * type_definition * variant_context) =
		let init_ctxs = (BatMap.empty, BatMap.empty, BatMap.empty, BatMap.empty) in  
		List.fold_left (fun (ec, tc, td, vc) decl ->
			match decl with 
			| TypeDeclaration (id, ty) ->
				let all_variants = extract_variants ty in
				let td' = BatMap.add id ty td in 
				let vc' = 
					List.fold_left (fun vc (ctor_id, arg_ty) ->
						BatMap.add ctor_id (arg_ty, Type.Named id) vc   
					) vc all_variants 
				in  
				(ec, tc, td', vc')  
  		| ExprDeclaration (id, e) ->
				let ec' = BatMap.add id (replace_holes ec e) ec in
				let ty = Typecheck.typecheck_exp ec' tc td vc e in
				let tc' = BatMap.add id ty tc in  
				(ec', tc', td, vc)   
		) init_ctxs decls
				
				
let process_spec (ec, _, _, _) (uspec:unprocessed_spec) : spec = 
	match uspec with 
	| UIOEs us ->
		(* TODO : typecheck examples *)
    let examples =
			List.map (fun (es,e) ->
        let vs = List.map (evaluate_with_context ec) es in
        let v = evaluate_with_context ec e in
				if (List.length vs) = 1 then
					(List.hd vs, v) 
				else 
        	(TupleV vs, v)
			) us
    in
    examples		
				
				
let process (unprocessed : t_unprocessed) : t =
  let (_,decls,synth_type,uspec) = unprocessed in
	let (ec,tc,td,vc) = process_decl_list decls in
  let synth_type = st_to_pair synth_type in
	let spec = process_spec (ec,tc,td,vc) uspec in
	{synth_type = synth_type; ec = ec; tc = tc; td = td; vc = vc; spec = spec}
	