.PHONY: build book core-check configure ide devcontainer-ide clean repl \
	html html-check html-clean serve docker-build docker-check docker-shell

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

# The book target is intentionally the same checked compilation as [build]:
# every literate chapter is listed in [_RocqProject].  Keeping a separate name
# makes the publishing workflow and the student-facing command self-documenting.
book: build core-check

# Exercise templates may contain [Admitted], but the trusted teaching library
# and completed examples must not.
core-check:
	@if rg -n '(^|[[:space:]])(Admitted|admit|Axiom)([[:space:].]|$$)' \
	  theories/Book theories/Preliminaries theories/Propositional \
	  theories/FirstOrder theories/Examples theories/Tactics.v; then \
		echo "Unexpected admission or axiom in the trusted teaching library."; \
		exit 1; \
	fi

html: book
	$(OPAM_EXEC) python3 tools/build_site.py build

html-check: html
	$(OPAM_EXEC) python3 tools/build_site.py check

html-clean:
	$(RM) -r _site

serve: html
	python3 -m http.server 8000 --directory _site

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
	$(RM) -r _site

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
