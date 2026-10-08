# PKU Mathematical Logic in Rocq

A small, teaching-oriented deep embedding of propositional and first-order logic
in the Rocq Prover. The development follows the first three chapters of Hanpin
Wang's mathematical logic textbook and emphasizes readable definitions,
explicit proof systems, and short pen-and-paper-style derivations.

## Build

Clone the repository before using either build method:

```console
git clone https://github.com/zhezhouzz/pku-mathematical-logic-rocq.git
cd pku-mathematical-logic-rocq
```

### Docker (recommended)

This method requires only [Docker](https://docs.docker.com/get-docker/). The
published image fixes the complete proof-toolchain version:

| Component | Version |
| --- | --- |
| Rocq | 9.1.1 |
| OCaml | 4.14.2 (flambda) |
| rocq-stdpp | 1.13.0 |
| VSRocq language server | 2.3.4 |

No host installation of OCaml, opam, Rocq, or std++ is required. The image also
includes Vim, Python 3 with `pip` and `venv`, ripgrep, and `tree` for convenient
interactive use. Pull the prebuilt image from Docker Hub:

```console
docker pull --platform linux/amd64 zhouzhe956/pku-mathematical-logic-rocq:rocq-9.1.1
```

Alternatively, build the same image locally from the pinned Dockerfile:

```console
make docker-build
```

The Dockerfile compiles all `.v` files while constructing the image, so a
successful image build also verifies the complete development. To rerun the
check without rebuilding the image:

```console
docker run --rm --platform linux/amd64 zhouzhe956/pku-mathematical-logic-rocq:rocq-9.1.1
```

For an interactive shell that uses the current checkout rather than the copy
baked into the image:

```console
docker run --rm -it \
  --platform linux/amd64 \
  -v "$PWD:/home/rocq/project" \
  -w /home/rocq/project \
  zhouzhe956/pku-mathematical-logic-rocq:rocq-9.1.1 bash
```

The equivalent convenience targets are `make docker-build`,
`make docker-check`, and `make docker-shell`. The explicit platform is needed
because the official Rocq 9.1 image is currently published for `linux/amd64`;
Docker Desktop can run it on Apple Silicon through emulation.

### Native opam installation

For editor integration or development without Docker, use
[opam](https://opam.ocaml.org/) 2.1 or later and a project-local OCaml switch.
Initialize opam once on the machine, create the switch, and install Rocq and
std++ from the official Rocq package repository:

```console
opam init
opam switch create . ocaml-base-compiler.4.14.2
eval "$(opam env --switch=. --set-switch)"
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-core=9.1.1 rocq-runtime=9.1.1 rocq-stdlib=9.0.0 \
  rocq-stdpp=1.13.0 vsrocq-language-server=2.3.4
rocq -v
make build
```

The Makefile runs Rocq through the opam switch selected for the current
directory. To use an existing named switch, install the same pinned packages
listed above in that switch and run
`OPAM_SWITCH=my-rocq-switch make build`.
Every build regenerates `RocqMakefile` and its dependency metadata because
those generated files contain environment-specific absolute paths. It is
therefore safe to alternate between native and bind-mounted Docker builds.
Other native targets are:

```console
make ide    # build .vo files used by editor integrations
make repl   # start a Rocq REPL with this project's logical path
make clean  # remove generated build artifacts
```

## Running and Editing

### VS Code Dev Container (recommended)

This workflow keeps the compiler, libraries, and VSRocq language server inside
the same versioned container. On the host, install only:

1. [Docker Desktop](https://docs.docker.com/get-docker/);
2. [Visual Studio Code](https://code.visualstudio.com/);
3. Microsoft's **Dev Containers** extension (`ms-vscode-remote.remote-containers`).

Install the extension from the VS Code Extensions view, or from a terminal:

```console
code --install-extension ms-vscode-remote.remote-containers
```

The `code` command is optional: if it is not available in the shell, install
the extension through the Extensions view and open the cloned repository with
**File > Open Folder**. Otherwise, start VS Code from the repository root:

```console
code .
```

Open the Command Palette (`Cmd+Shift+P` on macOS or `Ctrl+Shift+P` on
Windows/Linux) and select:

```text
Dev Containers: Reopen in Container
```

VS Code reads `.devcontainer/devcontainer.json` and automatically pulls
`zhouzhe956/pku-mathematical-logic-rocq:rocq-9.1.1` if it is not already
available. It then:

- mounts the current checkout at `/home/rocq/project`, so edits remain in the
  host repository;
- installs the VSRocq extension (`rocq-prover.vsrocq`) inside the container;
- uses `/home/rocq/bin/vsrocqtop` from the pinned toolchain; and
- runs `make devcontainer-ide` to compile the project for editor use.

The first start can take several minutes while Docker downloads the image and
VS Code installs the remote extension. When it finishes, the lower-left corner
of VS Code shows that the window is connected to the development container.
Open a terminal inside that window and verify the environment if desired:

```console
rocq -v
ocamlc -version
which vsrocqtop
make ide
```

No host installation of Rocq, OCaml, opam, std++, or VSRocq is used by this
workflow. If the repository was previously opened with another Rocq/OCaml
toolchain, `make devcontainer-ide` detects incompatible `.vo` files and
rebuilds them automatically.

### Inspecting proofs in VS Code

Open a `.v` file, place the cursor after a command, and use VSRocq's
**Interpret to Point** command. **Step Forward** and **Step Backward** process
one command at a time, while the VSRocq Goals panel displays the current goals,
hypotheses, and messages. Useful starting points are:

- `theories/Examples/TruthTables.v`
- `theories/Examples/NProofs.v`
- `theories/Examples/PProofs.v`
- `theories/Examples/FirstOrder.v`
- `theories/Exercises/NExercises.v`
- `theories/Exercises/PExercises.v`

If these commands or the Goals panel do not appear, open the Extensions view
while connected to the container and confirm that **VSRocq** is enabled under
"Dev Container" rather than only under "Local". Do not enable VSRocq and a
second Rocq language-server extension for the same workspace.

After changing `Dockerfile` or a pinned dependency, run `make docker-build` on
the host and select **Dev Containers: Rebuild Container**. To switch from an
older already-running configuration to the published versioned image, select
**Dev Containers: Rebuild and Reopen in Container**.

### Docker command line

To work without VS Code, start an interactive shell whose project directory is
the current host checkout:

```console
make docker-shell
```

Then compile or start the Rocq REPL inside the container:

```console
make devcontainer-ide
make repl
```

Use `Ctrl+D` or `exit` to leave the container. For a non-interactive full
compilation check, run `make docker-check` on the host.

### Native VS Code setup

If the native opam installation above is used instead of Docker, install the
VSRocq VS Code extension on the host:

```console
code --install-extension rocq-prover.vsrocq
eval "$(opam env --switch=. --set-switch)"
make ide
code .
```

Starting VS Code after `opam env` lets the extension find the language server
from the project-local switch. If VS Code still cannot find it, obtain the
absolute path with:

```console
opam exec -- which vsrocqtop
```

Set **VSRocq: Path** (`vsrocq.path`) in the workspace settings to that absolute
path, restart VS Code, and use the same **Interpret to Point**, **Step Forward**,
and **Step Backward** commands described above.

## Project Overview

The library is deliberately small. It exposes object-language syntax,
semantics, and derivation trees directly, so that students can inspect and
construct the mathematical objects discussed in class. It includes four proof
systems:

| System | Logic | Style | Judgment |
| --- | --- | --- | --- |
| N | Propositional logic | Natural deduction | `Γ ⊢ₙ A` |
| P | Propositional logic with primitive `¬` and `→` | Hilbert system | `Γ ⊢ₚ A` |
| N<sub>L</sub> | First-order logic | Natural deduction | `Γ ⊢ₙₗ A` |
| K<sub>L</sub> | First-order logic | Hilbert system | `Γ ⊢ₖ A` |

Contexts and variable collections are finite sets implemented with std++
`gset`. The four systems use separate judgments, and their connective
notations live in `N_scope`, `P_scope`, and `FOL_scope`. The same familiar
symbols—`¬`, `∧`, `∨`, `→`, and `↔`—can therefore be reused without confusing
the underlying syntax. Object-language quantifiers are written `∀ₒ` and `∃ₒ`
because the unadorned symbols are Rocq's meta-language binders.

The project contains a modest amount of supporting metatheory needed for
teaching and exercises, including weakening, substitution/cut, derived natural
deduction rules, and the deduction theorem for the Hilbert systems. It does not
aim to be a comprehensive metatheory library.

## Repository Structure

```text
theories/
├── Tactics.v
├── Propositional/
│   ├── Syntax.v
│   ├── Semantics.v
│   ├── NaturalDeduction.v
│   ├── DerivedRules.v
│   └── Hilbert.v
├── FirstOrder/
│   ├── Syntax.v
│   ├── Semantics.v
│   ├── NaturalDeduction.v
│   └── Hilbert.v
├── Examples/
└── Exercises/
```

- `Propositional/Syntax.v` defines formulas, complexity, depth, variables, and
  finite contexts.
- `Propositional/Semantics.v` defines Boolean valuations, truth tables,
  validity, satisfiability, and semantic consequence `Γ ⊨ A`.
- `Propositional/NaturalDeduction.v` defines system N and its structural
  results; `DerivedRules.v` gives common derived rules with readable proofs.
- `Propositional/Hilbert.v` defines system P, its axioms, modus ponens, and the
  deduction theorem.
- `FirstOrder/Syntax.v` defines terms, formulas, free variables, substitutability,
  and substitution.
- `FirstOrder/Semantics.v` gives Tarski semantics and first-order semantic
  consequence.
- `FirstOrder/NaturalDeduction.v` and `FirstOrder/Hilbert.v` define systems
  N<sub>L</sub> and K<sub>L</sub>.
- `Tactics.v` provides small tactics for normalizing finite-set contexts.
- `Examples/` contains scripts intended for line-by-line classroom execution.
- `Exercises/` contains worksheets and solutions organized around Chapters 2
  and 3 of the textbook.
- `Dockerfile` and `.dockerignore` define the reproducible container build;
  `Makefile` provides both native and Docker entry points.
- [`TEXTBOOK_COVERAGE.md`](TEXTBOOK_COVERAGE.md) maps textbook sections,
  theorems, and exercises to source files.

## Using the Development

### Applying inference rules

Proof-system constructors are named by system: `N_...`, `P_...`, `NL_...`,
and `K_...`. Parameters that Rocq can recover from the conclusion or a proof
argument are implicit; genuinely undetermined intermediate formulas remain
available as named arguments.

```rocq
Open Scope N_scope.

Example identity (A : formula) : (∅ : Context) ⊢ₙ (A → A).
Proof.
  apply N_impIntro.
  n_assumption.
Qed.
```

Typical applications include:

```rocq
apply N_impIntro.                       (* Γ, A, and B follow from the goal *)
exact (N_impElim proofAB proofA).       (* A follows from the two premises *)
exact (N_conjElimLeft proofAB).         (* B follows from proofAB *)
apply (N_disjElim (A := A) (B := B)).   (* name formulas not yet constrained *)
```

Use `About N_impElim.` to inspect a rule's complete type and its implicit
arguments.

### Normalizing contexts

The teaching tactics hide routine finite-set rearrangement while leaving the
logical inference step visible:

```rocq
normalize_context.
normalize_context_to ({[A; B]} : Context).
```

The first tactic removes empty sets and duplicate insertions and normalizes
associativity. The second proves equality with a requested normal form using
std++'s set solver.

### Truth tables and semantic consequence

`truth_table` is a record containing the variables and rows of a truth table.
`printTruthTable` renders it as a list of strings suitable for evaluation in an
editor:

```rocq
Compute printTruthTable (Imp (Atom "p") (Atom "p")).
```

The notation `Γ ⊨ A` denotes semantic consequence: every valuation or model
that satisfies all formulas in `Γ` also satisfies `A`. This is distinct from a
derivability judgment such as `Γ ⊢ₙ A`, whose inhabitant is a derivation tree
built from the rules of system N.

## References

1. Hanpin Wang. *Mathematical Logic (Discrete Mathematics, Volume I)*
   [《数理逻辑（离散数学一分册）》]. Course textbook, in Chinese.
2. The Rocq Prover Development Team. [The Rocq Prover documentation](https://rocq-prover.org/docs/).
3. The Rocq community. [Docker images of the Rocq Prover](https://github.com/rocq-community/docker-rocq).
4. The std++ developers. [Rocq-std++: an extended standard library for Rocq](https://gitlab.mpi-sws.org/iris/stdpp).
5. Haskell B. Curry and Robert Feys. *Combinatory Logic, Volume I*.
   North-Holland, 1958.
