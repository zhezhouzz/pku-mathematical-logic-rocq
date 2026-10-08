.PHONY: build ide clean repl docker-build docker-check docker-shell

OPAM ?= opam
OPAM_SWITCH ?=
OPAM_EXEC = $(OPAM) exec $(if $(OPAM_SWITCH),--switch=$(OPAM_SWITCH)) --
DOCKER ?= docker
DOCKER_IMAGE ?= pku-mathematical-logic-rocq
DOCKER_PLATFORM ?= linux/amd64

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

docker-build:
	$(DOCKER) build --platform $(DOCKER_PLATFORM) -t $(DOCKER_IMAGE) .

docker-check:
	$(DOCKER) run --rm --platform $(DOCKER_PLATFORM) $(DOCKER_IMAGE)

docker-shell:
	$(DOCKER) run --rm -it --platform $(DOCKER_PLATFORM) \
		-v "$(CURDIR):/home/rocq/project" \
		-w /home/rocq/project \
		$(DOCKER_IMAGE) bash
