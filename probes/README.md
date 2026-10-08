# Probes

Standalone Coq files that check one design claim each. They are not part
of the build (`_CoqProject` lists `theories/` only). Compile one with
`coqc <file>` inside the dev shell.

- `UipProbe.v`: `sEq` irrelevance, `transp` into any motive, and
  propositional β at `srefl` together prove UIP for `Id`
  (`M10_DESIGN.md` S6).
- `IwfProbe.v`: the `IWf` former of Heather's `docs/iwf-former-design.md`.
  It checks the derived `dnth` with a first-order family, β on open data
  at a computed index, fording's F2/F3 lowerings, and index inversion
  (`M10_DESIGN.md` S8).
- `NoUipComponents.v`: the components lemma of Heather's
  `docs/no-uip-model.md` §3, over reflexive-graph contexts with groupoid
  fibres. It checks that the strict propositions (`sEq`, `Squash`,
  `sEmpty`) are families, are strictly stable under substitution and are
  definitionally irrelevant. It also checks `srefl`, `elim_sEmpty` and
  `ElimSquash`, that `transp` at a strict motive exists, and, in the
  groupoid of types and bijections, that a relevant `transp` does not
  exist and UIP at `Ty 0` fails, at `Bool`, the carrier of the
  development's `UIP0` (`no_uip0`), and at `Nat`, the carrier of its
  `UIP0_nat` (`no_uip0_nat`; both in `theories/Validity/Uip.v`).
- `NoUipJ.v`: `Id` and Paulin-Mohring's `J` in the groupoid model of
  `docs/no-uip-model.md` (§2, §4.5), for `J` as `wf_J` states it. It uses
  lawful groupoids whose objects and morphisms form sets, split families,
  and sections with their functor laws. It builds `Id(a↑; var 0)` over
  `Γ.A` as a split family, `refl`, and `J` as a section of `M[u/y, e/p]`
  with both functor laws, and proves β on the nose. It also proves
  stability under substitution: `J(M; c; u; e)[σ] = J(M[σ⁺⁺]; c[σ]; u[σ];
  e[σ])` (`J_stab_ob`, `J_stab_hom`). `Id` and `refl` are stable by
  conversion. `J_example` shows that the hypotheses are satisfiable.
- `SquashProbe.v`: Heather's `Squash` term relation (MX §27), refined so
  that a `squash`'s payload is related to itself, stated over the
  development's logical relation with the former abstract. It checks the
  PER laws, escape, symmetry, irrelevance and weak-head expansion
  (`HEATHER.md`, Findings). It needs the theories compiled: `coqc -Q
  theories DeLaM probes/SquashProbe.v` (or `-vok` after `make vos`).
