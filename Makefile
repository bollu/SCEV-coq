# Coq sources
COQDIR = coq
COQLIBDIR = lib

# OCaml sources
MLDIR = 

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) SCEV)
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES := SCEV

VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq

coq: $(VOFILES)



%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend



# Directories containing plain Caml code
OCAMLDIRS= $(EXTRACTDIR) $(MLDIR) 

COMMA=,
OCAMLINCLUDES=$(patsubst %,-I %, $(OCAMLDIRS))
print-ocaml-includes:
	@echo $(OCAMLINCLUDES)

OCAMLLIBS := unix,str

.PHONY: clean main.native test qc restore

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	ocamlbuild -clean
	rm -rf output
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll


.PHONY: documentation
documentation: doc/coq2html $(VFILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

-include .depend

install:
	echo "HOW TO INSTALL?"
