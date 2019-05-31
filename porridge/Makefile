default: all
	@echo
	@echo 'Build successful!'
	@echo 'You may now run "make install", or play with "src/porridge".'

%:
	make -C src $@

tarball:
	rm -rf porridge
	mkdir -p porridge/src
	cp README.md Makefile porridge.opam porridge
	cp src/*ml src/*.mli src/Makefile src/META porridge/src
	tar cjvf porridge.tar.bz2 porridge
