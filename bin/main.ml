open Options

let main () = 
    let src = ref "" in
    let usage = Printf.sprintf "Usage: %s <options> <file>" Sys.argv.(0) in
    let _ = Arg.parse options
                (fun x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given"))
								)
                usage
    in
		if !src = "" then Arg.usage options usage
    else
			(* let start = Sys.time () in *)
			let inc = open_in !src in
			let unprocessed_spec =
  			let lexbuf = Lexing.from_channel inc in
  			lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = !src };
  			Parser.unprocessed_problem Lexer.token lexbuf
			in
			let _ = close_in inc in
			(* prerr_endline (Specification.show_t_unprocessed unprocessed_spec); *)
			let spec = Specification.process unprocessed_spec in
			(* prerr_endline (Specification.show spec); *)
			let spec =
				let src_ty, dst_ty = (fst spec.synth_type, snd spec.synth_type) in 
				let tc = spec.tc in 
				let tc = BatMap.add Expr.target_func (Type.Arrow(src_ty, dst_ty)) tc in
				let tc = BatMap.add Expr.target_func_arg src_ty tc in   
				{spec with tc = tc} 
			in 
			let e = 
				try
					Bidirectional.synthesis spec
				with Generator.SolutionFound sol ->
				(* a solution is found while generating components *) 
				Generator.wrap spec sol  
			in 
			prerr_endline (Expr.show e)
		 
let _ = main ()
