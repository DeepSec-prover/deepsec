EXECUTABLE = deepsec
TESTING = test_deepsec
NAME_PROGRAMME = DeepSec
VERSION = 1.0alpha
SOURCE = Source/
### Compiler

# For bytecode compilation, unset NATIVECODE below or run:
#  make NATIVECODE="" <target>

PROFIL=
OCAMLOPT=$(if $(PROFIL),ocamloptp -p -P a,ocamlopt)
OCAMLDEP=ocamldep -native
OCAMLDOC=ocamldoc


### Compiler options
INCLUDES_MOD = str.cmxa
INCLUDES = -I $(SOURCE)core_library -I $(SOURCE)testing
# Compiler options specific to OCaml version >= 4
V4OPTIONS=$(if $(shell $(OCAMLOPT) -version | grep '^4'),-bin-annot)
OCAMLFLAGS = $(INCLUDES) $(V4OPTIONS) -w Ae $(INCLUDES_MOD)

### Sources

GENERATED_SOURCES_NAME = testing_grammar.ml testing_lexer.ml testing_grammar.mli
GENERATED_SOURCES = $(GENERATED_SOURCES_NAME:%=$(SOURCE)testing/%)

CORE_ML_NAME = config.ml display.ml term.ml
CORE_ML = $(CORE_ML_NAME:%.ml=$(SOURCE)core_library/%.ml)

TESTING_ML_NAME = testing_functions.ml testing_parser_functions.ml testing_grammar.ml testing_lexer.ml
TESTING_ML = $(TESTING_ML_NAME:%.ml=$(SOURCE)testing/%.ml)

ALL_ML = $(CORE_ML) $(TESTING_ML) $(SOURCE)main.ml $(SOURCE)testing/testing.ml

EXE_MAIN_ML = $(CORE_ML) $(TESTING_ML) $(SOURCE)main.ml
EXE_TESTING_ML = $(CORE_ML) $(TESTING_ML) $(SOURCE)testing/testing.ml

ALL_OBJ = $(ALL_ML:.ml=.cmx)
EXE_MAIN_OBJ = $(EXE_MAIN_ML:.ml=.cmx)
EXE_TESTING_OBJ = $(EXE_TESTING_ML:.ml=.cmx)

### Targets

all: .display_obj $(ALL_OBJ)
	@echo
	@echo The main executable:
	@echo
	$(OCAMLOPT) -o $(EXECUTABLE) $(OCAMLFLAGS) $(EXE_MAIN_OBJ)
	@echo
	@echo The executable for testing:
	@echo
	$(OCAMLOPT) -o $(TESTING) $(OCAMLFLAGS) $(EXE_TESTING_OBJ)
	@echo
	@echo ----- Some Statistics -----
	@echo
	@echo Number of line of the program :
	@find . -name "*.ml" -or -name "*.mli" -or -name "*.mly" -or -name "*.mll" | xargs cat | wc -l
	@rm -f .display .display_obj

clean:
	@echo ----- Clean $(NAME_PROGRAMME) -----
	rm -f $(EXECUTABLE) $(TESTING)
	rm -f *~ *.cm[ioxt] *.cmti *.o
	rm -f */*~ */*.cm[ioxt] */*.cmti */*.o
	rm -f */*/*~ */*/*.cm[ioxt] */*/*.cmti */*/*.o
	rm -f $(GENERATED_SOURCES)
	rm -f .depend .display .display_obj

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

.SUFFIXES: .ml .mli .cmx .cmi .mll .mly

.ml.cmx:
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	ocamlyacc $<

### Dependencies

.depend: .display $(CORE_ML) $(GENERATED_SOURCES)
	@echo
	@echo The Dependencies
	@echo
	$(OCAMLDEP) $(INCLUDES) $(ALL_ML) $(GENERATED_SOURCES) > .depend

-include .depend
