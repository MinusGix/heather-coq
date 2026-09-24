# DeLaM formalization

A Coq formalization of DeLaM (Hu & Pientka, *A Dependent Layered Modal Type
Theory for Meta-programming*), following the paper's own normalization proof:
a Kripke logical relation over reduction with a generic equivalence
instantiated twice (Abel, Öhman & Vezzosi 2017), in the architecture of
[logrel-coq](https://github.com/CoqHott/logrel-coq), made `Prop`-valued so
the universe hierarchy and level polymorphism fit (see
`../logrel-coq-spike/SPIKE_UNIVERSES.md`).

Status: **Milestone 1 (MLTT core) in progress.** Syntax, declarative
typing with its syntactic metatheory (weakening, substitution, stability,
functionality, presupposition), the generic-equivalence interface with the
declarative instance, and the logical relation with escape, irrelevance,
symmetry and transitivity are done. No admits, no axioms.
See `M1_DESIGN.md` §"Status" for what's done and the ordered next steps.

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
