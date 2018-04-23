# This is a supplementary evaluation repository for the paper "Improving Refutational Completeness of Relational Search via Divergence Test"

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

Building, evaluating, and generating the report:

* `make` - makes OCanren + performance tests, runs all the tests (takes some time) and generates a .tex file;
* `pdflatex main` - builds report (some generic TeX installation is required).



