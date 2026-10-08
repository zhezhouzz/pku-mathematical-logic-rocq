.PHONY: build configure ide devcontainer-ide clean repl docker-build docker-check docker-shell

OPAM ?= opam
OPAM_SWITCH ?=
OPAM_EXEC = $(OPAM) exec $(if $(OPAM_SWITCH),--switch=$(OPAM_SWITCH)) --
DOCKER ?= docker
DOCKER_IMAGE ?= zhouzhe956/pku-mathematical-logic-rocq:rocq-9.1.1
DOCKER_PLATFORM ?= linux/amd64

# Generated Rocq makefiles contain absolute toolchain paths. Regenerate them
# whenever the active opam switch or container may have changed.
configure:
	$(RM) RocqMakefile RocqMakefile.conf .RocqMakefile.d
	$(OPAM_EXEC) rocq makefile -f _RocqProject -o RocqMakefile

# Build .vo files next to the teaching sources so that VsRocq can resolve
# [Require] commands using [_RocqProject].
ide: configure
	$(OPAM_EXEC) $(MAKE) -f RocqMakefile

build: ide

# A bind-mounted workspace may contain .vo files produced by another OCaml
# toolchain. Test a central library before starting VSRocq, and rebuild only
# when the existing object files cannot be loaded by this container.
devcontainer-ide:
	@if [ -f theories/Propositional/Syntax.vo ] && \
	   ! $(OPAM_EXEC) rocq repl -batch -Q theories LogicCourse \
	     -require-import LogicCourse.Propositional.Syntax >/dev/null 2>&1; then \
		echo "Removing Rocq object files built by an incompatible toolchain."; \
		$(MAKE) clean; \
	fi
	@$(MAKE) ide

clean: configure
	$(OPAM_EXEC) $(MAKE) -f RocqMakefile clean
	$(RM) RocqMakefile RocqMakefile.conf .RocqMakefile.d

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
