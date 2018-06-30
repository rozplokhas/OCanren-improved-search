OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
SOURCES = $(wildcard *_*_*.ml)
BUILD = ../_build
CAMLP5 = -pp "camlp5o pr_o.cmo -I `ocamlfind -query logger.syntax` -I $(BUILD)/camlp5 -I `ocamlfind -query GT.syntax` pa_log.cmo pa_minikanren.cmo pa_gt.cmo -L `ocamlfind -query GT.syntax`"
PXFLAGS = $(CAMLP5)
BFLAGS = -rectypes -I `ocamlfind -query GT` -I $(BUILD)/src 
OFLAGS = $(BFLAGS)

all: tester.cmx OptimisticDefinitions.cmx PessimisticImprovedDefinitions.cmx OptimisticImprovedDefinitions.cmx PessimisticDefinitions.cmx $(SOURCES:.ml=.opt)

evaluate: all
	@rm -f ../evaluation_defs.tex log \\
	@for F in $(SOURCES:.ml=.opt); do echo "Evaluating $$F..." ; OCAMLRUNPARAM='s=250M,h=250M' ./$$F >> log 2>>  ../evaluation_defs.tex ; done

%.opt: %.ml
	$(OCAMLOPT) -o $@ $(CAMLP5) $(OFLAGS) GT.cmxa unix.cmxa MiniKanren.cmxa tester.cmx OptimisticDefinitions.cmx PessimisticImprovedDefinitions.cmx OptimisticImprovedDefinitions.cmx PessimisticDefinitions.cmx $<

clean:
	rm -Rf *.cmi *.cmo *.cmx *.annot *.o *.opt

# generic rules

###############
%.cmi: %.mli
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

# Note: cmi <- mli should go first
%.cmi: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.o: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

