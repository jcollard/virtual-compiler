

all: Main.native

Main.native: Main.ml VirtualCompiler.ml
	ocamlbuild -use-ocamlfind -pkgs core,ocamlgraph -tag thread Main.native

clean:
	rm _build Main.native *~ -rf
