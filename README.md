#This is a supplementary evaluation repository for the paper "Improving Refutational Completeness of Relational Search via Divergence Test"

Prerequisites:

* [ocaml](ocaml.org)
* [opam](opam.ocaml.org)

Installation:

* `opam install findlib`
* `opam install ocamlbuild`
* `opam install camlp5`
* `opam pin add GT https://github.com/dboulytchev/GT.git`
* `opam pin add logger https://github.com/dboulytchev/logger.git`
* `opam install GT`
* `opam install logger`

Building:

* `make` (this makes OCanren + performance tests)

Evaluating:

* `make evaluate` (this runs all tests; takes some time)



