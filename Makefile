NAME_PROGRAMME = DeepSec
VERSION = 1.02
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
PHYSICALCORE = $(shell script/cpu_linux_osx)
NBLINE = $(shell find . -name "*.ml" -or -name "*.mli" -or -name "*.mly" -or -name "*.mll" | xargs cat | wc -l)

# whole compilation
all:
	@printf "\033[1mCompilation of DeepSec $(VERSION)\033[0m\n"
	@echo $(CORES)
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
	@sed -e "s/VERSION/${VERSION}/g" -e "s/GITCOMMIT/${GITCOMMIT}/g" -e "s/GITBRANCH/${GITBRANCH}/g" -e "s/PHYSICALCORE/${PHYSICALCORE}/g" < Source/core_library/config.ml.in > Source/core_library/config.ml

# configures and compiles
compil:
	@ocamlbuild $(PACKAGES) main.$(EXTENSION) worker.$(EXTENSION) manager.$(EXTENSION) main_ui.$(EXTENSION)
	@mv `ls -l main.$(EXTENSION) | sed 's/^.* -> //'` deepsec
	@mv `ls -l main_ui.$(EXTENSION) | sed 's/^.* -> //'` deepsec_api
	@mv `ls -l worker.$(EXTENSION) | sed 's/^.* -> //'` worker_deepsec
	@mv `ls -l manager.$(EXTENSION) | sed 's/^.* -> //'` manager_deepsec
	rm main.$(EXTENSION) main_ui.$(EXTENSION) worker.$(EXTENSION) manager.$(EXTENSION)
	@printf "\033[1mBuild successful!\033[0m You can invoke ./deepsec alone to display version data, or ./deepsec -help for usage information.\n\033[1mNumber of lines in the source code: $(NBLINE)\033[0m\n"

# checks installation requirements
check:
	@printf "\033[1mChecking installation requirements...\033[0m\n"
	@$(SCRIPTS)check

# removes automatically generated files
clean:
	rm -rf _build $(SOURCE)core_library/config.ml $(TEMP) deepsec worker_deepsec manager_deepsec deepsec_api
