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
