.PHONY: build ide clean repl

OPAM ?= opam
OPAM_SWITCH ?=
OPAM_EXEC = $(OPAM) exec $(if $(OPAM_SWITCH),--switch=$(OPAM_SWITCH)) --

# Build .vo files next to the teaching sources so that VsRocq can resolve
# [Require] commands using [_RocqProject].
RocqMakefile: _RocqProject
	$(OPAM_EXEC) rocq makefile -f _RocqProject -o RocqMakefile

ide: RocqMakefile
	$(OPAM_EXEC) $(MAKE) -f RocqMakefile

build: ide

clean:
	@if [ -f RocqMakefile ]; then $(OPAM_EXEC) $(MAKE) -f RocqMakefile clean; fi

repl:
	$(OPAM_EXEC) rocq repl -Q theories LogicCourse
