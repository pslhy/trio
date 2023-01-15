.PHONY: build
build:
	dune build bin/main.exe

.PHONY: clean
clean:
	dune clean

.PHONY: deps
deps:
	opam install menhir batteries dune 

