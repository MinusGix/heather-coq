# DeLaM formalization: notes for agents

Start by reading `README.md`, then `HEATHER.md` (Heather's extensions: the
forward agenda), `M11_DESIGN.md` (current milestone), `M10_DESIGN.md`, `M9_DESIGN.md`,
`M8_DESIGN.md`, `M7_DESIGN.md`, `M6_DESIGN.md`, `M5_DESIGN.md`,
`M4_DESIGN.md`, `M3_DESIGN.md`, `M2_DESIGN.md` and `M1_DESIGN.md`. The latter holds the M1
current status, the ordered next steps, deviations from the paper, and a
list of proof-engineering gotchas. Follow it.

## Context

- Goal: formalize DeLaM plus the user's extensions (more layers, possibly a
  2D code/program layer structure, "Encode the Cake"-style local computation
  rules). This repo replaces an earlier McTT-based attempt
  (`../refs/McTT`, frozen). The paper's own proof follows Abel et al. 2017;
  logrel-coq (`../refs/logrel-coq`) is the architectural template.
- Paper sources: `../heather/docs/delam/*.tex`. Ch. 4 = rules, ch. 5 =
  substitutions, ch. 6 = reduction, ch. 7 / 07a / 07b = logical relation,
  validity, fundamental theorem.
- Spikes that fixed the design: `../logrel-coq-spike/SPIKE_UNIVERSES.md`
  (the relation must be `Prop`-valued) and `SYNTAX_SPIKE.md` (hand-written
  syntax, with the representation of local/global substitutions).

## Build

- `nix develop path:. --command make -j2` (Coq 8.20, Equations, smpl from
  the flake). A clean build takes under 4 minutes (234 s wall, 2026-09-30,
  after M11b; 168 s before M11a, down from 8.5 minutes). The critical path (Syntax → Typing metatheory →
  Validity → the algorithm) is nearly the whole build, so more jobs don't
  help; only faster files on that path do. `make TIMING=1` writes per-file
  `.v.timing`; the build-time gotchas in `M1_DESIGN.md` list the patterns
  that made it slow.
- Fast iteration: `make -j2 vos` (about 1 minute from clean) compiles every
  file's statements without its proofs; then check the file you are working
  on in full with `coqc -Q theories DeLaM -vok <file>` (or `make vok`, which
  checks every file's proofs, in parallel). Neither replaces the final
  `make`. A section lemma's proof is skipped by `vos` only with a
  `Proof using` clause: the six heaviest sectioned files have them
  (`tools/add_proof_using.py`).
- Probe goals by truncating a proof into a scratch file and compiling with
  `coqc -Q theories DeLaM <file>` inside the dev shell.

## Working style (user preferences)

- Write proof code directly in the tree. Keep the build green and commit
  at each checkpoint (narrow commits, descriptive messages).
- Verified, not asserted: check claims with Coq. No admits or axioms
  without flagging them. propext + funext are the only expected axioms, and
  only where the design notes say so.
- Avoid positional hypothesis names and bullets that break when
  constructors are added. Select by goal and hypothesis shape.
- Discuss first only on genuine design forks. Otherwise pick the sensible
  default and record it in the design doc.
- Multi-agent workflows only when the user explicitly asks.
