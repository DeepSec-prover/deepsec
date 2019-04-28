PACKAGES = -package str -package unix
INCLUDES = -I Source/subterms -I Source/distributed -I Source/core_library -I Source/parser
TEMP = *.native index.html result
EXECUTABLE = deepsec
SOURCE = Source/


# configures and compiles
compil:
	$(SOURCE)configure
	ocamlbuild -use-ocamlfind $(PACKAGES) $(INCLUDES) $(SOURCE)main.native
	mv main.native $(EXECUTABLE)


# documentation
doc:
	ocamlbuild -use-ocamlfind $(PACKAGES) $(INCLUDES) doc.docdir/index.html doc.docdir/doc.tex
	./Documentation/finishdoc




GENERATED_SOURCES_NAME = parser/grammar.ml parser/lexer.ml parser/grammar.mli
GENERATED_SOURCES = $(GENERATED_SOURCES_NAME:%=$(SOURCE)%)

# removes automatically generated files
clean:
	rm -rf _build $(SOURCE)core_library/config.ml $(TEMP)
	rm -f $(EXECUTABLE) worker_deepsec manager_deepsec
	# cleaning remainder of other branches
	rm -f *~ *.cm[ioxt] *.cmti *.o
	rm -f */*~ */*.cm[ioxt] */*.cmti */*.o
	rm -f */*/*~ */*/*.cm[ioxt] */*/*.cmti */*/*.o */*/*.output
	rm -f $(GENERATED_SOURCES)
	rm -f .depend .display .display_obj
