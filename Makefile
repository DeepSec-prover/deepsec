NAME_PROGRAMME = DeepSec
VERSION = 2.0.2
SOURCE = Source/
SCRIPTS = script/
BINDIR = ~

PACKAGES = -package str -package unix
TEMP = *.native *.p.native *.d.byte result

# for profiling or advanced debugging, set the variables below to 1
PROFILE= # seems broken on OSX 10.9 or later
ADVDEBUG=
EXTENSION=$(if $(PROFILE),p.native,$(if $(ADVDEBUG),d.byte,native))

GITC = $(shell git rev-parse HEAD 2> /dev/null)
ifeq ($(GITC),)
GITCOMMIT="not_available"
else
GITCOMMIT = $(GITC)
endif

GITB = $(shell git branch 2> /dev/null | grep \* | sed -E "s/^\* \(?//" | sed -E "s/\)$$//" )
ifeq ($(GITB),)
GITBRANCH="not_available"
else
GITBRANCH = $(GITB)
endif



PHYSICALCORE_SCRIPT = $(shell $(SCRIPTS)/cpu_linux_osx 2> /dev/null)
ifeq ($(PHYSICALCORE_SCRIPT),0)
PHYSICALCORE = 1
else
PHYSICALCORE = $(PHYSICALCORE_SCRIPT)
endif
OSTYPE = $(shell uname)
NBLINE = $(shell find Source -name "*.ml" -or -name "*.mli" -or -name "*.mly" -or -name "*.mll" | xargs cat | wc -l)

.PHONY: check


# whole compilation
all:
	@printf "\e[1mCompilation of DeepSec $(VERSION)\e[0m\n"
	@echo
	@make -s core_check git_check
	@printf "\e[1mBuilding sources$(if $(PROFILE), (PROFILE on),$(if $(ADVDEBUG), (ADVDEBUG on),))...\e[0m\n"
	@make -s config compil

# same, but activates debugging functions in the code (for development only)
debug:
	@printf "\e[1mCompiling DeepSec (debugging functions on)...\e[0m\n"
	@make -s config
	@sed /debug_activated/s/false/true/ Source/core_library/config.ml > .tmp.ml
	@mv .tmp.ml Source/core_library/config.ml
	@make -s compil

# Check the number of physical core
core_check:
	@if [ $(PHYSICALCORE_SCRIPT) -eq 0 ]; then \
		if [ $(OSTYPE) = 'Darwin' ]; then \
	    printf "\e[33m\e[1mWarning:\e[0m Could not detect the number of physical core of your machine (most probably sysctl is not installed). Set to 1.\n"; \
	  else \
			printf "\e[33m\e[1mWarning:\e[0m Could not detect the number of physical core of your machine (most probably lscpu is not installed). Set to 1.\n"; \
		fi \
	fi

git_check:
	@if [ -z "$(GITCOMMIT)" ]; then \
		printf "\e[33m\e[1mWarning:\e[0m Could not detect the git branch or git commit. Cloning the git repository is recommended for bug report and updates.\n"; \
	fi

# Check the presen

# generates config.ml
config:
	@sed -e "s/VERSION/${VERSION}/g" -e "s/GITCOMMIT/${GITCOMMIT}/g" -e "s/GITBRANCH/${GITBRANCH}/g" -e "s/PHYSICALCORE/${PHYSICALCORE}/g" -e "s/OSTYPE/${OSTYPE}/g" < Source/core_library/config.ml.in > Source/core_library/config.ml

# configures and compiles
compil:
	@ocamlbuild -use-ocamlfind $(PACKAGES) main.$(EXTENSION) worker.$(EXTENSION) main_api.$(EXTENSION)
	@mv _build/Source/main.$(EXTENSION)  deepsec
	@mv _build/Source/main_api.$(EXTENSION) deepsec_api
	@mv _build/Source/distributed/worker.$(EXTENSION) deepsec_worker
	rm main.$(EXTENSION) main_api.$(EXTENSION) worker.$(EXTENSION)
	@printf "\e[32m\e[1mBuild successful!\033[0m You can invoke ./deepsec alone or with option --help to display version data and usage information.\n\033[1mNumber of lines in the source code: $(NBLINE)\e[0m\n"

# checks installation requirements
check:
	@printf "\e[1mChecking installation requirements...\e[0m\n"
	@$(SCRIPTS)check

# moving executables
install:
	@cp deepsec $(BINDIR)
	@cp deepsec_api $(BINDIR)
	@cp deepsec_worker $(BINDIR)

# removes automatically generated files
clean:
	rm -rf _build $(SOURCE)core_library/config.ml $(TEMP) deepsec deepsec_worker deepsec_api
