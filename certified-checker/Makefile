install: compile test
	mkdir -p ../bin
	cp _build/Interface.native ../bin/certified-checker
clean:
	rm -fv *.vo *.o *.glob *.hi Interface.native Checker.ml Checker.mli
	rm -frv _build
%.vo: %.v
	coqc $<
test:
	./Interface.native ../examples/example1.cnf ../examples/example1.grit
compile: Map.vo Fset.vo Mapaxioms.vo Mapiter.vo Mapsubset.vo Lsort.vo Mapfold.vo Mapcard.vo Mapcanon.vo Mapc.vo Maplists.vo Adalloc.vo Allmaps.vo Basic.vo BinaryTrees.vo SetChecker.vo
	coqc Extraction.v
	rm -rf _build Interface.native *.o
	ocamlbuild -use-ocamlfind Interface.native
