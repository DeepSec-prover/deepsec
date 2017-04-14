VERSION=1.0alpha
NAME_PROGRAMME = DeepSec

PATH_SOURCE = ../Source/

INCLUDES = -I $(PATH_SOURCE) -I $(PATH_SOURCE)core_library -I $(PATH_SOURCE)subterms -I $(PATH_SOURCE)testing


NAME_STANDARD = Core_library
FILE_STANDARD = config.mli display.mli term.mli process.mli
PATH_STANDARD = $(FILE_STANDARD:%= $(PATH_SOURCE)core_library/%)

NAME_SUBTERMS = Subterms
FILE_SUBTERMS = data_structure.mli constraint_system.mli equivalence.mli
PATH_SUBTERMS = $(FILE_SUBTERMS:%= $(PATH_SOURCE)subterms/%)

NAME_TESTING = Testing
FILE_TESTING = testing_functions.mli testing_load_verify.mli testing.ml
PATH_TESTING = $(FILE_TESTING:%= $(PATH_SOURCE)testing/%)


# Starting Point

main: display standard subterms testing
	@echo
	@echo Compilation of the .pdf file :
	@echo
	latex main
	bibtex main || true
	latex main
	dvipdf -dPDFSETTINGS=/prepress -dEmbedAllFonts=true main

# Module Standard Library

HIDDEN_MODULE = Pervasives,Term,Data_structure

standard:
	@echo
	@echo Compilation of the $(NAME_STANDARD).tex file:
	@echo
	ocamldoc.opt -hide $(HIDDEN_MODULE) -latextitle 4,subparagraph -noheader -notrailer -o $(NAME_STANDARD).tex -latex $(INCLUDES) $(PATH_STANDARD)

subterms:
	@echo
	@echo Compilation of the $(NAME_SUBTERMS).tex file:
	@echo
	ocamldoc.opt -hide $(HIDDEN_MODULE) -latextitle 4,subparagraph -noheader -notrailer -o $(NAME_SUBTERMS).tex -latex $(INCLUDES) $(PATH_SUBTERMS)


testing:
	@echo
	@echo Compilation of the $(NAME_TESTING).tex file:
	@echo
	ocamldoc.opt -hide $(HIDDEN_MODULE) -latextitle 4,subparagraph -noheader -notrailer -o $(NAME_TESTING).tex -latex $(INCLUDES) $(PATH_TESTING)


# Display

display:
	@echo ----------------------------------------------
	@echo         Documentation of $(NAME_PROGRAMME) $(VERSION)
	@echo ----------------------------------------------

# Cleaning
clean: clean_tool
	@echo ----- Clean documentation of $(NAME_PROGRAMME) $(VERSION) -----
	rm -f main.aux main.bbl main.blg main.dvi main.log main.out main.pdf main.toc *~

# Tool

tool:
	@cd ../Source/;make

clean_tool:
	@cd ../Source/;make clean
