.PHONY: build ide clean repl

OPAM_SWITCH := with-rocq-1

# Build .vo files next to the teaching sources so that VsRocq can resolve
# [Require] commands using [_RocqProject].
RocqMakefile: _RocqProject
	opam exec --switch=$(OPAM_SWITCH) -- rocq makefile -f _RocqProject -o RocqMakefile

ide: RocqMakefile
	opam exec --switch=$(OPAM_SWITCH) -- $(MAKE) -f RocqMakefile

build: ide

clean:
	@if [ -f RocqMakefile ]; then opam exec --switch=$(OPAM_SWITCH) -- $(MAKE) -f RocqMakefile clean; fi

repl:
	opam exec --switch=$(OPAM_SWITCH) -- rocq repl -Q theories LogicCourse
