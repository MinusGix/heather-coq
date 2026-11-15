# DeLaM in Coq

A machine-checked metatheory of **DeLaM**, a dependent type theory in
which programs can build, inspect and run code of the same language, and
of the extensions that the [Heather](https://github.com/MinusGix/heather)
theorem prover's kernel adds to it.

DeLaM is due to Hu and Pientka (*A Dependent Layered Modal Type Theory
for Meta-programming*). This repository proves its main properties in Coq
8.20: about 230 files and 110,000 lines, with **no admitted lemmas and no
axioms**.

- [In plain terms](#in-plain-terms)
- [What is proved](#what-is-proved)
- [What the theory contains](#what-the-theory-contains)
- [How the proof works](#how-the-proof-works)
- [Repository layout](#repository-layout)
- [Milestones](#milestones)
- [Building](#building)
- [Further reading](#further-reading)

## In plain terms

A *proof assistant* such as Coq, Lean or Agda is a programming language
whose type checker is strict enough that a well-typed program can serve
as a mathematical proof. Its rules form a *type theory*, and the whole
tool is only as trustworthy as that theory: if the rules can derive a
contradiction, every "proof" is worthless.

Real proof assistants also need *meta-programs*: programs that write
proofs and programs (tactics, automation, code generators). Today these
are usually written in a separate language (Ltac, OCaml plugins, Lean's
`MetaM`) that cannot state, in its types, what the code it produces
means. DeLaM's idea is to let the theory talk about its own code:

- A type `□ T` holds a *piece of code* of type `T`: syntax, not a value.
- A meta-program can take code apart by its structure (pattern match on
  it, recurse over it), and can also *run* it.
- Meta-programs can abstract over contexts, types and universe levels,
  so a single tactic-like function works generically.

The danger is that "code" and "value" disagree. As values, `2 + 2` and
`4` are equal, and the type checker treats them as interchangeable. As
code they are different trees, and a meta-program can tell them apart.
If both views lived in one place, the theory could prove `2 + 2 ≠ 4` and
`2 + 2 = 4` at once.

DeLaM separates them with **layers**. Every judgment says which layer it
lives at:

| Layer | Holds | Computes? | Meta-programming? |
|---|---|---|---|
| **V** | variables only (the base case when recursing over code) | no | no |
| **C** | code: ordinary type theory, treated as syntax | no | no |
| **D** | programs: ordinary type theory, with computation | yes | no |
| **M** | meta-programs: everything in D plus code, its analysis and polymorphism | yes | yes |

Code at layer C never computes, so the analysis sees exactly the syntax
that was written. Programs at D compute but cannot look inside code.
Only layer M can do both, and it can only inspect code from the layers
below it. (The paper calls layer D "P", for programs.)

This repository proves that this design holds together: the theory is
consistent, every program computes to an answer, and type checking can
be done by a terminating algorithm. It then does the same for each
feature Heather adds on top: pairs, sums, equality types, inductive and
coinductive data, definitions, and more. Some of Heather's rules were
changed or removed because of what these proofs found (see `HEATHER.md`,
"Findings").

## What is proved

At the computing layers D and M, for the whole theory with every
extension below. The names are Coq statements in `theories/`.

| Result | In plain terms | Where |
|---|---|---|
| **Consistency** | No closed term has type `Π (X : Ty ℓ). El X` (that is, falsehood has no proof); also with definitions in scope | `consistency` in `Validity/Consistency.v`; `consistency_def` in `Validity/ConsistencyDef.v` |
| **Normalization** | Every well-typed type and term reduces to a weak-head normal form | `whnf_normalization_ty_c`, `whnf_normalization_tm_c` in `Validity/Uniform.v` |
| **Canonicity** | A closed term computes to a value of its type: a `Nat` to a numeral, a pair type to a pair, and so on for every former | `closed_canonicity` and its corollaries in `Validity/Canonicity.v` |
| **Injectivity of type formers** | `Π A B ≡ Π A' B'` implies `A ≡ A'` and `B ≡ B'`, and distinct formers are never equal | `Validity/Consequences.v`, `Validity/TyInj.v` |
| **Subject reduction** | Reduction preserves types | `preservation_tm`, `preservation_ty` in `Validity/Preservation.v` |
| **Decidable conversion** | An algorithm decides whether two well-typed terms are definitionally equal, and it is sound and complete | `decl_eqty_dec`, `decl_eqtm_dec` in `Validity/AlgDec.v` |
| **Decidable type checking** | Whether a term has a type is decidable, at every layer | `wf_ty_dec`, `wf_tm_dec` in `Validity/TypeCheck.v` |
| **Static Code** | At layers V and C, equal code is syntactically equal (up to universe-level arithmetic) | `static_code_eq` in `Typing/StaticCodeEq.v` |
| **The paper's own rules** | The paper's rule set for its fragment, transcribed over our syntax, derives nothing ours does not, so consistency and canonicity hold for it too | `paper_sound` in `Validity/PaperSound.v`, over `Typing/Paper.v` |

`make assumptions` runs `Print Assumptions` on the headline statements
(`checks/Assumptions.v`); each prints "Closed under the global context".

## What the theory contains

**From the paper (milestones M1 to M7).**
- *The base*: dependent functions `Π`, natural numbers, a hierarchy of
  universes `Ty ℓ` with level variables, in Tarski style (a code `t` is
  turned into a type by `El t`).
- *Code*: the box type `□` of code in a local context, `box`, `letbox`
  (run code), and the two mutually recursive *code recursors*
  `elim_Typ`/`elim_Trm`, which fold over the syntax of a piece of code.
- *Meta-level abstraction*: functions over universe levels (`UΠ`, with
  the limit level ω), over local contexts (`CΠ`) and over types (`TΠ`).

**Heather's extensions (M8 on).** Each goes through the whole stack:
typing rules, the logical relation, the fundamental theorem, the
algorithm, decidability and canonicity, and then gets a *code* so that
meta-programs can analyse it (new branches of the code recursor: 61 in
all, against the paper's 13).

| Feature | What it is | Milestone |
|---|---|---|
| `Σ`, `Unit` | dependent pairs and the unit type, both with η | M8 |
| definitions | global constants with bodies that unfold (δ) | M9 |
| `sEq`, `sEmpty` | strict, proof-irrelevant equality and falsehood | M10 |
| `Id`, `refl`, `J` | the identity type | M11 |
| `Empty`, `+` | the empty type and binary sums | M12 |
| `W` | well-founded trees (general inductive types) | M13 |
| `Vec`, `Fin` | length-indexed tuples and bounded numbers | M14 |
| `Wf` | well-founded trees with finitely many children | M15 |
| `∥A∥` | propositional truncation | M16 |
| `DVec`, `IWf` | dependent tuples; indexed inductive families | M17 |
| `M`, `corec`, `out` | indexed coinductive types (infinite data) | M18 |

## How the proof works

This section assumes some type theory; the design notes have the full
story.

The proof follows the paper's, which follows Abel, Öhman and Vezzosi,
*Decidability of conversion for type theory in type theory* (2017),
in the architecture of [logrel-coq](https://github.com/CoqHott/logrel-coq):

1. **Syntax** (`theories/Syntax`). De Bruijn indices; types and terms
   are separate sorts (Tarski universes); every judgment carries its
   layer and its universe level, `G ; Γ ⊢[i] t : T @ l`. The syntax is
   hand-written rather than generated, because DeLaM's global
   substitutions and code scopes fall outside what Autosubst can express
   (`docs/design/SYNTAX_SPIKE.md`). Universe-level equivalence is
   defined semantically, as equality under every valuation.
2. **Typing** (`theories/Typing`). The declarative rules and their
   metatheory: weakening, the three substitutions (local, global,
   universe), inversion, presupposition, Static Code. The rules are
   stated against an abstract *generic equivalence*, so that one
   development serves two notions of equality.
3. **Logical relation** (`theories/LogRel`). A Kripke logical relation
   over reduction, indexed by universe level and by layer (`j ∈ {D, M}`),
   quantified over local and global weakenings. It is
   `Prop`-valued (unlike logrel-coq's), which is what lets the universe
   hierarchy and level polymorphism fit; this was settled by an earlier
   spike outside this repository. Its properties: escape, symmetry,
   transitivity, irrelevance, weakening, reflection of neutrals and
   closure under weak-head expansion.
4. **Validity and the fundamental theorem** (`theories/Validity`). Every
   typing rule is shown valid in the relation, one file per former, so
   every well-typed term is in the relation (`FundamentalS`,
   `FundamentalM`). The consequences follow: normalization, injectivity,
   canonicity, consistency.
5. **The algorithm.** The generic equivalence is instantiated a second
   time with an algorithmic convertibility check. Running the
   fundamental theorem again with that instance gives completeness, and
   with soundness, decidability of conversion and then of type checking
   (`Validity/Alg*.v`, `Validity/TC*.v`).

The design notes record every place where the formalization departs
from the paper and why; `M1_DESIGN.md` lists the deviations the rest
builds on.

## Repository layout

| Path | Contents |
|---|---|
| `theories/Syntax/` | terms, levels, renaming and the three substitutions, reduction, normal forms (29 files) |
| `theories/Typing/` | the declarative judgments and their metatheory, the generic equivalence, the code recursors' specification, the paper's rule set (`Paper.v`) (58 files) |
| `theories/LogRel/` | the logical relation and its properties (17 files) |
| `theories/Validity/` | validity per former, the fundamental theorems, the algorithm, decidability, type checking and the consequences (125 files) |
| `checks/` | the axiom check, run by `make assumptions` |
| `probes/` | standalone Coq files that test one design question each before it enters the theories; see `probes/README.md` |
| `spike/` | the syntax spike that fixed the representation |
| `docs/design/` | one design note per milestone, plus cross-cutting notes; index in `docs/design/README.md` |
| `docs/gotchas.md` | proof-engineering and build-time lessons |
| `HEATHER.md` | Heather's extensions: what this repo checks of them, the findings, the plan |
| `tools/` | build profiling and the fast iteration loop (each script documents itself) |
| `CLAUDE.md` | working notes for contributors and coding agents: build loop, conventions |

Inside `theories/`, a file is named after what it proves, and a former's
files carry its name (`Validity/Sigma.v`, `Validity/W.v`, `Validity/WElim.v`,
…). Large files are split into parts that build in parallel
(`RecS*.v`, `AlgPER*.v`, `LevelEq*.v`), with the old name kept as the
file that re-exports them.

## Milestones

Each milestone adds one feature through the whole stack. Its design note
in `docs/design/` records the decisions and the outcome; the full status
list is in [`docs/design/README.md`](docs/design/README.md#milestones-in-detail).

| | Milestone | Note |
|---|---|---|
| M1 | The MLTT core, through the fundamental theorem | `M1_DESIGN.md` |
| M2 | The modal core: global variables, `□`, `box`, `letbox` | `M2_DESIGN.md` |
| M3 | Universe substitutions and the code recursors | `M3_DESIGN.md` |
| M4 | Universe polymorphism (`UΠ`, ω) | `M4_DESIGN.md` |
| M5 | Abstraction over contexts and types (`CΠ`, `TΠ`) | `M5_DESIGN.md` |
| M6 | Algorithmic conversion and its decidability | `M6_DESIGN.md` |
| M7 | Consistency, canonicity, type checking, the paper's rule set | `M7_DESIGN.md` |
| M8 | `Σ` and `Unit` with η | `M8_DESIGN.md` |
| M9 | Definitions | `M9_DESIGN.md` |
| M10 | Strict equality | `M10_DESIGN.md` |
| M11 | The identity type | `M11_DESIGN.md` |
| M12 | `Empty`, sums, Hedberg's theorem | `M12_DESIGN.md` |
| M13 | `W` types | `M13_DESIGN.md` |
| M14 | `Vec`, `Fin` | `M14_DESIGN.md` |
| M15 | `Wf` | `M15_DESIGN.md` |
| M16 | Propositional truncation | `M16_DESIGN.md` |
| M17 | `DVec`, `IWf` | `M17_DESIGN.md` |
| M18 | Coinductive `M` (codes, M18c, wait on Heather) | `M18_DESIGN.md` |

What comes next is in `HEATHER.md`, "Proposed order".

## Building

With [Nix](https://nixos.org) (flakes enabled):

```sh
nix develop path:. --command make -j4      # the whole development
nix develop path:. --command make assumptions   # check that no axioms crept in
```

The flake pins Coq 8.20, Equations and smpl. A clean build takes 10 to 25
minutes on four cores. For a quicker check of every proof,
`make -j4 vos && make -j4 vok` compiles the statements first and then
checks all proofs in parallel. A single probe compiles with `coqc` inside
the dev shell, as `probes/README.md` describes.

Contributors: `CLAUDE.md` has the inner loop (cached build trees, a
persistent proof session), the profiling tools and the conventions, and
`docs/gotchas.md` the patterns that made proofs slow or brittle.

## Further reading

- `HEATHER.md`: what Heather's kernel adds to DeLaM, where its designs
  live, the cross-checks between the two, and the plan.
- `docs/design/README.md`: the design notes, indexed, and the
  milestone-by-milestone status.
- `probes/README.md`: the standalone probes and what each settled.
- The paper sources are in Heather's repository, `docs/delam/`: chapter 4
  has the rules, 5 the substitutions, 6 reduction, 7 the logical
  relation and the fundamental theorem.
