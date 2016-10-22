# grit
certified and uncertified checkers for the General ResolutIon Trace (GRIT) format


The subdirectories contain:
* c-checker: an uncertified C-implemented GRIT checker (fast!)
* certified-checker: a certified GRIT checker extracted from Coq to Ocaml (correct!)
* drat-trim: a version of drat-trim modified to output GRIT files (pre-processor)
* examples: examples of CNF, RUP, and GRIT files
* iglucose: glucose for incremental SAT solving (produces RUP proofs)
* lingeling: SAT solver in 2016 competition version (produces RUP proofs)
* ocaml-set-checker: another certified GRIT checker extracted from Coq to Ocaml (faster than certified-checker)
* py-checker: an uncertified Python-implemented GRIT checker (READABLE!)


At least the following software packages are required for building:
* Coq theorem prover (tested with coqc 8.4pl3)
* GNU C Compiler (tested with gcc 4.8.4)
* GNU coreutils (tested with tac 8.2.1)
* GNU Make (tested with make 3.81)
* OCaml (tested with ocamlbuild 4.01.0)
* Python (tested with python 2.7.6)


To run a SAT solver on a non-trivial example and verify the result:

  make
  scripts/solve-verify.sh examples/slp-synthesis-aes-bottom12.cnf


Notes for Mac OS X users:
* tac can be installed using e.g. homebrew (but will be called gtac)
    brew install coreutils
    ln -s /usr/local/bin/gtac /usr/local/bin/tac
* the HFS+ is by default case-insensitive, resulting in problems
  when compiling lingeling more than once (Makefile vs makefile)
