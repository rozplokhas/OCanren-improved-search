OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
SOURCES = $(wildcard *_*_*.ml)
BUILD = ../_build
CAMLP5 = -pp "camlp5o pr_o.cmo -I `ocamlfind -query logger.syntax` -I $(BUILD)/camlp5 -I `ocamlfind -query ostap.syntax` -I `ocamlfind -query GT.syntax` pa_log.cmo pa_minikanren.cmo pa_ostap.cmo pa_gt.cmo -L `ocamlfind -query GT.syntax`"
PXFLAGS = $(CAMLP5)
BFLAGS = -rectypes -I `ocamlfind -query ostap` -I `ocamlfind -query GT` -I $(BUILD)/src -I `ocamlfind -query re` 
OFLAGS = $(BFLAGS)

all: tester.cmx ExtendedDefinitions.cmx $(SOURCES:.ml=.opt)

%.opt: %.ml
	$(OCAMLOPT) -o $@ $(CAMLP5) $(OFLAGS) GT.cmxa re.cmxa emacs/re_emacs.cmxa str/re_str.cmxa ostap.cmx unix.cmxa MiniKanren.cmxa tester.cmx ExtendedDefinitions.cmx $<

clean:
	rm -Rf *.cmi *.cmo *.cmx *.annot *.o

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

