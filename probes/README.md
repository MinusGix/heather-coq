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
  exist and UIP at `Ty 0` fails, at `Bool` (`no_uip0`) and at `Nat`,
  the carrier of the development's `UIP0` (`no_uip0_nat`,
  `theories/Validity/Uip.v`).
