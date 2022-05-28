open Vocab

type t =
  | Named of string
  | Arrow of t * t
  | Tuple of t list
  | Variant of (string * t) list (* e.g., [ ("O", Tuple []) ; ("S", Named "nat") ] *)
[@@deriving eq, ord, show]

let compare t1 t2 = 
	(* unit type is the smallest one *)
	match t1, t2 with 
	Tuple [], _ -> -1
	| _, Tuple [] -> 1 
	| _ -> compare t1 t2 

let rec show t = 
	match t with 
	| Named i -> i 
	| Arrow (t1, t2) -> Printf.sprintf "(%s -> %s)" (show t1) (show t2) 
	| Tuple ts -> string_of_list ~first:"(" ~last:")" ~sep:", " show ts
	| Variant its ->
		string_of_list ~first:"" ~last:"" ~sep:"\n | " 
			(fun (i,t) -> Printf.sprintf "%s of %s" i (show t)) its 
		  
type variants = (string * t) list
[@@deriving eq, ord, show]


let _unit : t = Tuple []

let _t = Named "t"

let _bool = Named "bool"

let _nat = Named "nat"

let is_named_type ty = 
	match ty with
	| Named _ -> true 
	| _ -> false 
	
let is_arrow_type ty = 
	match ty with 
	| Arrow _ -> true 
	| _ -> false 

let is_tuple_type ty = 
	match ty with 
	| Tuple _ -> true 
	| _ -> false 

let is_variant_type ty = 
	match ty with 
	| Variant _ -> true 
	| _ -> false 


let destruct_arrow t = 
	match t with 
	| Arrow (t1, t2) -> (t1, t2) 
	| _ -> failwith "destruct_arrow"

let destruct_tuple t = 
	match t with 
	| Tuple ts -> ts 
	| _ -> failwith "destruct_tuple"

let destruct_variant t = 
	match t with 
	| Variant ts -> ts 
	| _ -> failwith "destruct_variant"
