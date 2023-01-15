# Trio 

Trio is a tool for synthesizing recursive functional programs from input-output examples. 
It takes as input (1) custom data types, (2) operators that may be used by a solution, and (3) a type signature for the solution to be synthesized and a set of input-output examples, and produces a recursive functional program that satisfies the input-output examples. 
A formal exposition of the system can be found in our POPL 23 publication, 
[Inductive Synthesis of Structurally Recursive Programs from Non-recursive Expressions](https://dl.acm.org/doi/10.1145/3571263).

## Installation

1. Install [`opam`](https://opam.ocaml.org/doc/Install.html), the OCaml package
   manager.

2. Install OCaml 4.10.0 with the
   [flambda](https://caml.inria.fr/pub/docs/manual-ocaml/flambda.html) optimizer
   by running `opam switch create 4.10.0+flambda`. OCaml versions after 4.10.0
   should work fine too, but are untested.

3. Run `make deps` in the root directory of this project to download all the
   necessary `opam` dependencies.

4. Run `make` to build the Trio executable. The executable is accessible via
   the `trio` symlink in the root directory of this project.

## Running the Tool
You can run Trio to solve a single benchmark as follows:
```
$ ./trio [trio options] [benchmark file]
```
For example, 
to solve the single benchmark in test/io/nat_mul.mls
```
$ ./trio test/io/nat_mul.mls
```

The following options are available. 
```
  -print_blocks Print all block expressions
  -get_size Get size of an expression
  -all Find all solutions and pick the smallest one
  -rec solution must be recursive
  -nofilter don't perform block-based pruning
  -noinvmap don't use inverse maps of external functions
  -debug print info for debugging
  -max_size set the maximum size of candidates
  -max_height set the maximum height of candidates
  -init_comp_size set the initial size of components
  -help  Display this list of options
  --help  Display this list of options
```

## Reproducing the Experimental Evaluation 

To reproduce the experimental evaluation in the paper, please refer to the 
following [link](https://github.com/pslhy/trio_artifacts). 
