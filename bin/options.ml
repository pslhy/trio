let debug = ref false
let max_size = ref 128
let max_height_vsa = ref 6
let max_height = ref 6
let init_comp_size = ref 5
let find_all = ref false 
let get_size = ref false 
let print_traces = ref false
let always_recursive = ref false 
let max_match_depth = ref 3 
let no_filter = ref false
let no_invmap = ref false
let options = 
	[
	 ("-print_blocks", Arg.Set print_traces, "Print all block expressions");	
	 ("-get_size", Arg.Set get_size, "Get size of an expression");
	 ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	
	 ("-rec", Arg.Set always_recursive, "solution must be recursive");	
	 ("-nofilter", Arg.Set no_filter, "don't perform block-based pruning");	
	 ("-noinvmap", Arg.Set no_invmap, "don't use inverse maps of external functions");	
	 ("-debug", Arg.Set debug, "print info for debugging");
	 ("-max_size", Arg.Int (fun x -> max_size := x), "set the maximum size of candidates");
	 ("-max_height", Arg.Int (fun x -> max_height := x), "set the maximum height of candidates");
	 ("-max_height_vsa", Arg.Int (fun x -> max_height_vsa := x), "set the maximum height of VSAs");
	 ("-init_comp_size", Arg.Int (fun x -> init_comp_size := x), "set the initial size of components");
  ]