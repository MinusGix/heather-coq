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

Milestone 4 (universe polymorphism: `UΠ`, `Λ`, `$` and the level ω) is in
design; see `M4_DESIGN.md`.

No admits, no axioms. See `M3_DESIGN.md`, `M2_DESIGN.md` and `M1_DESIGN.md`
for decisions, deviations from the paper and gotchas.

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
