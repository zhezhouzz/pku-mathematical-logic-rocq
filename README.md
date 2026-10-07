# PKU Mathematical Logic in Rocq

A small, teaching-oriented deep embedding of propositional and first-order logic
in the Rocq Prover. The development follows the first three chapters of Hanpin
Wang's mathematical logic textbook and emphasizes readable definitions,
explicit proof systems, and short pen-and-paper-style derivations.

## Build

### Prerequisites

The recommended setup uses [opam](https://opam.ocaml.org/) 2.1 or later and a
project-local OCaml switch. This keeps the Rocq installation for this project
separate from any system-wide or pre-existing Rocq installation.

First install opam using the instructions for your operating system, then clone
the repository:

```sh
git clone https://github.com/zhezhouzz/pku-mathematical-logic-rocq.git
cd pku-mathematical-logic-rocq
```

Initialize opam if this is its first use on the machine:

```sh
opam init
```

Create a local switch, add the official Rocq package repository, and install
Rocq together with std++:

```sh
opam switch create . ocaml-base-compiler.4.14.2
eval "$(opam env --switch=. --set-switch)"
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-prover rocq-stdpp
```

The project uses `rocq-stdpp` for finite sets and their proof automation. opam
will select versions of Rocq and std++ that are compatible with one another.
Confirm the installation and compile every source file with:

```sh
rocq -v
make build
```

The Makefile runs Rocq through the opam switch selected for the current
directory. To use an existing named switch instead, install `rocq-prover` and
`rocq-stdpp` in that switch and run, for example:

```sh
OPAM_SWITCH=my-rocq-switch make build
```

Other useful targets are:

```sh
make ide    # build .vo files used by editor integrations
make repl   # start a Rocq REPL with this project's logical path
make clean  # remove generated build artifacts
```

### Editor setup

For interactive use in VS Code or Cursor, install the VSRocq extension and its
language server in the same opam switch:

```sh
opam install vsrocq-language-server
```

Open the repository directory itself as the editor workspace. In a `.v` file,
use **Interpret to Point**, **Step Forward**, and **Step Backward** to process
the script incrementally. Good starting points are:

- `theories/Examples/TruthTables.v`
- `theories/Examples/NProofs.v`
- `theories/Examples/PProofs.v`
- `theories/Examples/FirstOrder.v`

Do not enable VSRocq and another Rocq language-server extension for the same
workspace at the same time.

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
3. The std++ developers. [Rocq-std++: an extended standard library for Rocq](https://gitlab.mpi-sws.org/iris/stdpp).
4. Haskell B. Curry and Robert Feys. *Combinatory Logic, Volume I*.
   North-Holland, 1958.
