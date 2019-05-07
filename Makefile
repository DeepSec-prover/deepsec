EXECUTABLE = deepsec
NAME_PROGRAMME = DeepSec
VERSION = 1.01
SOURCE = Source/
### Compiler

# For bytecode compilation, unset NATIVECODE below or run:
#  make NATIVECODE="" <target>
DEBUG=
PROFIL=
OCAMLOPT=$(if $(PROFIL),ocamloptp -p -P a,$(if $(DEBUG), ocamlc -g,ocamlopt))
OCAMLDEP=ocamldep $(if $(DEBUG), ,-native)
OCAMLDOC=ocamldoc

GITCOMMIT=$(head -n 1 <(git rev-parse HEAD 2>/dev/null))
GITBRANCH=$(git branch | grep \* | cut -d ' ' -f2)


CMOX= $(if $(DEBUG),cmo,cmx)
CMXA= $(if $(DEBUG),cma,cmxa)

### Compiler options
INCLUDES_MOD = str.$(CMXA) unix.$(CMXA)
INCLUDES = -I $(SOURCE)core_library -I $(SOURCE)subterms -I $(SOURCE)parser -I $(SOURCE)distributed
# Compiler options specific to OCaml version >= 4
V4OPTIONS=$(if $(shell $(OCAMLOPT) -version | grep '^4'),-bin-annot)
OCAMLFLAGS = $(INCLUDES) $(V4OPTIONS) -w +a-44-e $(INCLUDES_MOD)

### Sources

GENERATED_SOURCES_NAME = parser/grammar.ml parser/lexer.ml parser/grammar.mli
GENERATED_SOURCES = $(GENERATED_SOURCES_NAME:%=$(SOURCE)%)

CORE_ML_NAME = extensions.ml display.ml term.ml process.ml process_determinate.ml process_session.ml
CORE_ML = $(CORE_ML_NAME:%.ml=$(SOURCE)core_library/%.ml)

SUBTERMS_ML_NAME = data_structure.ml constraint_system.ml equivalence.ml equivalence_determinate.ml equivalence_session.ml
SUBTERMS_ML = $(SUBTERMS_ML_NAME:%.ml=$(SOURCE)subterms/%.ml)

DISTRIBUTED_ML_NAME = distrib.ml distributed_equivalence.ml
DISTRIBUTED_ML = $(DISTRIBUTED_ML_NAME:%.ml=$(SOURCE)distributed/%.ml)

PARSER_ML_NAME = parser_functions.ml grammar.ml lexer.ml
PARSER_ML = $(PARSER_ML_NAME:%.ml=$(SOURCE)parser/%.ml)

ALL_ML = $(SOURCE)core_library/config.ml $(CORE_ML) $(SUBTERMS_ML) $(PARSER_ML) $(DISTRIBUTED_ML) $(SOURCE)main.ml $(SOURCE)distributed/worker.ml $(SOURCE)distributed/manager.ml

EXE_MAIN_ML = $(SOURCE)core_library/config.ml $(CORE_ML) $(SUBTERMS_ML) $(PARSER_ML) $(DISTRIBUTED_ML) $(SOURCE)main.ml
EXE_WORKER_ML = $(SOURCE)core_library/config.ml $(CORE_ML) $(SUBTERMS_ML) $(PARSER_ML) $(DISTRIBUTED_ML) $(SOURCE)distributed/worker.ml
EXE_MANAGER_ML = $(SOURCE)core_library/config.ml $(CORE_ML) $(SUBTERMS_ML) $(PARSER_ML) $(DISTRIBUTED_ML) $(SOURCE)distributed/manager.ml

ALL_OBJ = $(ALL_ML:.ml=.$(CMOX))
EXE_MAIN_OBJ = $(EXE_MAIN_ML:.ml=.$(CMOX))
EXE_WORKER_OBJ = $(EXE_WORKER_ML:.ml=.$(CMOX))
EXE_MANAGER_OBJ = $(EXE_MANAGER_ML:.ml=.$(CMOX))

.PHONY: clean debug without_debug


### Targets

all: .display_obj $(ALL_OBJ)
	@sed -e 's/GITCOMMIT/$(GITCOMMIT)/g' -e's/VERSION/$(VERSION)/g' -e 's/GITBRANCH/${GITBRANCH}/g' < Source/core_library/config.ml.in > Source/core_library/config.ml
	@echo
	@echo The main executable:
	@echo
	$(OCAMLOPT) -o $(EXECUTABLE) $(OCAMLFLAGS) $(EXE_MAIN_OBJ)
	@echo
	@echo The executables for distributed worker:
	@echo
	$(OCAMLOPT) -o worker_deepsec $(OCAMLFLAGS) $(EXE_WORKER_OBJ)
	$(OCAMLOPT) -o manager_deepsec $(OCAMLFLAGS) $(EXE_MANAGER_OBJ)
	@echo
	@grep -q "let debug_activated = false" Source/core_library/config.ml || echo WARNING : Debug mode is activated; echo
	@grep -q "let test_activated = false" Source/core_library/config.ml || echo WARNING : Testing interface is activated; echo
	@test -e index.html || cp Source/html_templates/index_init.html index.html
	@echo ----- Some Statistics -----
	@echo
	@echo Number of lines in the source code of the program :
	@find . -name "*.ml" -or -name "*.mli" -or -name "*.mly" -or -name "*.mll" | xargs cat | wc -l
	@rm -f .display .display_obj


clean:
	@echo ----- Clean $(NAME_PROGRAMME) -----
	rm -f $(EXECUTABLE) worker_deepsec manager_deepsec
	rm -f $(SOURCE)core_library/config.ml
	rm -f *~ *.cm[ioxt] *.cmti *.o
	rm -f */*~ */*.cm[ioxt] */*.cmti */*.o
	rm -f */*/*~ */*/*.cm[ioxt] */*/*.cmti */*/*.o */*/*.output
	rm -f $(GENERATED_SOURCES)
	rm -f .depend .display .display_obj

debug:
	@echo Prepare the compilation of deepsec for debugging
	@sed /debug_activated/s/false/true/ Source/core_library/config.ml > .tmp.ml
	@mv .tmp.ml Source/core_library/config.ml
	@echo
	@echo To complete the compilation, you should run make

without_debug:
	@echo Prepare the compilation of deepsec to run without debugging
	@sed /debug_activated/s/true/false/ Source/core_library/config.ml > .tmp.ml
	@mv .tmp.ml Source/core_library/config.ml
	@echo
	@echo To complete the compilation, you should run make

#testing:
#	@echo Prepare the compilation of deepsec for generating tests
#	@sed /test_activated/s/false/true/ Source/core_library/config.ml > .tmp.ml
#	@mv .tmp.ml Source/core_library/config.ml
#	@echo
#	@echo To complete the compilation, you should run make

#without_testing:
#	@echo Prepare the compilation of deepsec to run without generation of tests
#	@sed /test_activated/s/true/false/ Source/core_library/config.ml > .tmp.ml
#	@mv .tmp.ml Source/core_library/config.ml
#	@echo
#	@echo To complete the compilation, you should run make

.display:
	@echo ----------------------------------------------
	@echo          Compilation of $(NAME_PROGRAMME) $(VERSION)
	@echo ----------------------------------------------
	@echo
	@echo Generation of files by the parsers and lexers
	@echo
	@touch .display

.display_obj:
	@echo
	@echo Generation of objects
	@echo
	@touch .display_obj

### Common rules

.SUFFIXES: .ml .mli .$(CMOX) .cmi .mll .mly

.ml.$(CMOX):
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	ocamlyacc -v $<

### Dependencies

.depend: .display $(CORE_ML) $(GENERATED_SOURCES)
	@echo
	@echo The Dependencies
	@echo
	@sed -e 's/GITCOMMIT/$(GITCOMMIT)/g' -e's/VERSION/$(VERSION)/g' < Source/core_library/config.ml.in > Source/core_library/config.ml
	$(OCAMLDEP) $(INCLUDES) $(ALL_ML) $(GENERATED_SOURCES) > .depend

-include .depend
