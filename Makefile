NAME_PROGRAMME = DeepSec
VERSION = 1.02
EXECUTABLE = deepsec
SOURCE = Source/
SCRIPTS = Scripts/

PACKAGES = -package str -package unix
TEMP = *.native *.p.native *.d.byte index.html result

# for profiling or advanced debugging, set the variables below to 1
PROFILE= # seems broken on OSX 10.9 or later
ADVDEBUG=
EXTENSION=$(if $(PROFILE),p.native,$(if $(ADVDEBUG),d.byte,native))

GITCOMMIT = $(shell git rev-parse HEAD)
GITBRANCH = $(shell git branch | grep \* | cut -d ' ' -f2)



# whole compilation
all:
	@printf "\033[1mBuilding sources$(if $(PROFILE), (PROFILE on),$(if $(ADVDEBUG), (ADVDEBUG on),))...\033[0m\n"
	@make -s config compil

# same, but activates debugging functions in the code (for development only)
debug:
	@printf "\033[1mCompiling DeepSec (debugging functions on)...\033[0m\n"
	@make -s config
	@sed /debug_activated/s/false/true/ Source/core_library/config.ml > .tmp.ml
	@mv .tmp.ml Source/core_library/config.ml
	@make -s compil

# generates config.ml
config:
	@$(SCRIPTS)configure $(VERSION) $(GITCOMMIT) $(GITBRANCH)

# configures and compiles
compil:
	@ocamlbuild -use-ocamlfind $(PACKAGES) $(SOURCE)main.$(EXTENSION) worker.$(EXTENSION) manager.$(EXTENSION)
	@mv main.$(EXTENSION) $(EXECUTABLE)
	@mv worker.$(EXTENSION) worker_deepsec
	@mv manager.$(EXTENSION) manager_deepsec
	@printf "\033[1mBuild successful!\033[0m You can invoke ./deepsec alone to display version data, or ./deepsec -help for usage information.\n"

# checks installation requirements
check:
	@printf "\033[1mChecking installation requirements...\033[0m\n"
	@$(SOURCE)check

# documentation
doc:
	@printf "\033[1mGenerating documentation...\033[0m\n"
	ocamlbuild -use-ocamlfind $(PACKAGES) doc.docdir/index.html doc.docdir/doc.tex
	@./Documentation/finishdoc


# removes automatically generated files
clean:
	rm -rf _build $(SOURCE)core_library/config.ml $(TEMP) $(EXECUTABLE) worker_deepsec manager_deepsec
