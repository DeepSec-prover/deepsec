PACKAGES = -package str -package unix
INCLUDES = -I Source/subterms -I Source/distributed -I Source/core_library -I Source/parser
TEMP = index.html result
EXECUTABLE = deepsec
SOURCE = Source/


# configures and compiles
compil:
	$(SOURCE)configure
	# ocamlbuild -use-ocamlfind $(PACKAGES) $(INCLUDES) $(SOURCE)main.native
	# mv main.native $(EXECUTABLE)
	ocamlbuild -use-ocamlfind $(PACKAGES) $(INCLUDES) $(SOURCE)core_library/operations.native

# removes automatically generated files
clean:
	rm -rf _build $(SOURCE)core_library/config.ml $(EXECUTABLE) $(TEMP)

# documentation
doc:
	ocamlbuild -use-ocamlfind $(PACKAGES) $(INCLUDES) doc.docdir/index.html doc.docdir/doc.tex
	./Documentation/finishdoc
