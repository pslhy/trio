let debug = ref false
let max_size = ref 32
let max_height = ref 6
let init_comp_size = ref 3
let find_all = ref false 
let get_size = ref false 
let print_traces = ref false
let always_recursive = ref false 
let options = 
	[
	 ("-print_traces", Arg.Set print_traces, "Print all trace expressions");	
	 ("-get_size", Arg.Set get_size, "Get size of an expression");
	 ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	
	 ("-rec", Arg.Set always_recursive, "solution must be recursive");	
	 ("-debug", Arg.Set debug, "print info for debugging");
	 ("-max_size", Arg.Int (fun x -> max_size := x), "set the maximum size of candidates");
	 ("-max_height", Arg.Int (fun x -> max_height := x), "set the maximum height of candidates");
	 ("-init_comp_size", Arg.Int (fun x -> init_comp_size := x), "set the initial size of components")
  ]