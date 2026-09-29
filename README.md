# DeLaM formalization

A Coq formalization of DeLaM (Hu & Pientka, *A Dependent Layered Modal Type
Theory for Meta-programming*), following the paper's own normalization proof:
a Kripke logical relation over reduction with a generic equivalence
instantiated twice (Abel, Öhman & Vezzosi 2017), in the architecture of
[logrel-coq](https://github.com/CoqHott/logrel-coq), made `Prop`-valued so
the universe hierarchy and level polymorphism fit (see
`../logrel-coq-spike/SPIKE_UNIVERSES.md`).

Status: **Milestones 1 (MLTT core) and 2 (modal core) complete.** M2 has:
- the syntax (global variables, contextual types, `box`, `letbox`);
- the declarative metatheory at every layer;
- the layered logical relation (`j ∈ {P, M}`, Kripke over global
  weakenings);
- the fundamental theorem with related global substitutions at layers
  C, P and M (`FundamentalS`, `FundamentalM`), which shows the Layering
  Restriction on the way;
- the consequences at P and M for arbitrary global contexts:
  - weak-head normalization;
  - injectivity and discrimination of type formers, including `□`;
  - canonicity for `Nat` and for contextual types.

Milestone 3 (universe substitutions and the code recursors) is also
complete:
- universe renaming and substitution, and the universe substitution lemma;
- validity quantified over universe substitutions;
- the recursors `elim_Typ`/`elim_Trm`, with their schematic β rules and
  the neutral recursion laws;
- the recursion lemmas and the fundamental theorem at M with the
  recursors. The consequences at M above still hold with the recursors
  included.

Milestone 4 (universe polymorphism: `UΠ`, `Λ`, `$` and the level ω) is
complete; see `M4_DESIGN.md`:
- the n-ary level binder, its β and η rules, and the typing metatheory;
- the relation at ω, a top tier over the finite relation;
- the fundamental theorem at M, with a finite half and an ω half;
- consequences at ω: normalization, injectivity of `UΠ` (bodies
  included), and discrimination of `UΠ` against the other type formers.

Milestone 5 (the meta-functions `CΠ` and `TΠ`: abstraction over local
contexts and over layer-P types) is complete; see `M5_DESIGN.md`:
- the syntax, the sixteen typing rules (β and η included) and the typing
  metatheory;
- two new cases of the relation at `j = M`, with every property;
- the semantic rules and the fundamental theorem at M;
- consequences: normalization, injectivity of `CΠ`/`TΠ` (bodies
  included), and discrimination against the other type formers.

Milestone 6 (algorithmic convertibility) is complete; see `M6_DESIGN.md`:
- the convertibility-checking judgments and their soundness;
- their structural properties, the conversion lemma, symmetry and
  transitivity;
- the lift of neutrals and the algorithmic instance of the generic
  equivalence, hence completeness through the fundamental theorems;
- decidability of algorithmic and of declarative equality of well-typed
  types and terms at D and M.

Milestone 7 (strengthening the base) is complete; see `M7_DESIGN.md`:
consistency, the paper's direction of Static Code, canonicity at every
type former, soundness of reduction and preservation, uniform statements
over D and M, and decidability of type checking for all terms at every
layer (the meta-level abstractions now carry their formers, a deviation
from the paper recorded in `M1_DESIGN.md`), with uniqueness of
synthesized types and the recursor rules without their scope premises.

From M8 on, the milestones check the extensions of Heather's kernel
(`HEATHER.md`):
- Milestone 8: Σ with η and `Unit` with η, as types and as code (eight
  new recursor branches), and the genericity work that made a new former
  cheap (shared generic laws, recursor branches through one lemma, rule
  lists); see `M8_DESIGN.md`.
- Milestone 9: bodied globals (definitions, δ at the computing layers);
  see `M9_DESIGN.md`, which also lists its open items.

No admits, no axioms. See the `M*_DESIGN.md` files (`M1_DESIGN.md` to
`M9_DESIGN.md`) for decisions, deviations from the paper and gotchas.

Documents:

- `M1_DESIGN.md`: milestone 1 scope, the shape decisions, deviations from
  the paper, status, next steps, and proof-engineering gotchas.
- `SYNTAX_SPIKE.md` / `spike/Syntax.v`: why the syntax is hand-written, and
  the representation, including the global-substitution part that the main
  tree doesn't contain yet.
- `../logrel-coq-spike/SPIKE_UNIVERSES.md`: why the logical relation must
  be `Prop`-valued.

Build: `nix develop path:. --command make` (main tree), spikes via the command
in each write-up.
