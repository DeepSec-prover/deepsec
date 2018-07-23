LIB = check.ml memo.ml utils.ml priority.ml \
	  hashcons.ml \
	  LTS.ml POR.ml \
	  SAList.ml channel.ml tm.ml frame.ml formula.ml process.ml \
	  constraints.ml sem_utils.ml trace_equiv.ml \
	  examples.ml
CHECK = $(LIB) check_main.ml

ML=$(wildcard *ml)
MLI=$(wildcard *mli)
CMO=$(ML:.ml=.cmo)

OCAMLCFLAGS=-g
OCAMLOPTFLAGS=-g

# The P flag is meant to be either empty or just "p"
# to switch from ocamlc/ocamlopt to ocamlcp/ocamloptp.
# Note that "make lib" won't work with these profiling
# compilers.
P=

OCAMLC=ocamlfind ocamlc$(P) $(OCAMLCFLAGS) -package alcotest
OCAMLOPT=ocamlfind ocamlopt$(P) $(OCAMLOPTFLAGS) -package alcotest

all: porridge.byte porridge ocamlpor test

lib: porridge.cma porridge.cmxa

install: porridge.cma porridge.cmxa
	ocamlfind install porridge META porridge.*

uninstall:
	ocamlfind remove porridge

clean:
	rm -f *.o *.a *.cmi *.cmo *.cma *.cmx *.cmxa
	rm -f check test porridge.byte porridge

doc: all
	mkdir -p ../doc
	ocamlfind ocamldoc -stars -package alcotest -html -d ../doc \
	  LTS.ml* POR.ml* \
	  channel.ml* tm.ml* frame.ml* process.ml* \
	  constraints.ml* formula.ml* sem_utils.ml* trace_equiv.ml*

%.cmo: %.ml
	$(OCAMLC) -c $<
%.cmi: %.mli
	$(OCAMLC) -c $<
%.cmx: %.ml
	$(OCAMLOPT) -for-pack Porridge -c $<

CHECK_CMO = $(CHECK:.ml=.cmo)

check: $(CHECK_CMO)
	$(OCAMLC) -linkpkg $(CHECK_CMO) -o check
test: check
	./check

porridge.cmo: $(LIB:.ml=.cmo)
	$(OCAMLC) $+ -pack -o $@
porridge.cma: porridge.cmo
	$(OCAMLC) $+ -a -o $@

porridge.cmx: $(LIB:.ml=.cmx)
	$(OCAMLOPT) $+ -opaque -pack -o $@
porridge.cmxa: porridge.cmx
	$(OCAMLOPT) $+ -opaque -a -o $@

porridge.byte: $(LIB:.ml=.cmo) main.cmo
	$(OCAMLC) -linkpkg $+ -o $@

porridge: $(LIB:.ml=.cmx) main.cmx
	$(OCAMLOPT) -linkpkg $+ -o $@

ocamlpor: lib
	ocamlfind ocamlmktop -package alcotest -linkpkg porridge.cma -o $@

# Profiling information

OCAMLPROF_FILES=$(LIB) main.ml
profiles:
	mkdir -p prof
	for i in $(OCAMLPROF_FILES) ; do OCAMLPROF_DUMP=/dev/null ocamlprof $$i > prof/$$i ; done

# Dependencies

-include .depend
.depend: $(ML) $(MLI)
	ocamldep *ml *mli > .depend
