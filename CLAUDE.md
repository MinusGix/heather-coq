# DeLaM formalization: notes for agents

Start by reading `README.md`, then `HEATHER.md` (Heather's extensions: the
forward agenda), `M16_DESIGN.md` (current milestone), `M15_DESIGN.md`, `M14_DESIGN.md`, `M13_DESIGN.md`, `M12_DESIGN.md`, `M11_DESIGN.md`, `M10_DESIGN.md`, `M9_DESIGN.md`,
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

- `nix develop path:. --command make -j4` (Coq 8.20, Equations, smpl from
  the flake). A clean build takes 10 to 22 minutes, depending on the
  machine. Latest: 748 s wall at -j4 after the 2026-10-12 dependency
  pass (Requires trimmed, wide files split), where the 2026-10-11 tree
  measured 903 s back to back on the same 4-core cloud machine
  (critical path 853 s → 687 s, total CPU 1440 s → 1466 s). Before that:
  876 s after the 2026-10-11 build-time pass, against 1107 s for M16a
  (critical path 1053 s → 826 s). Machines differ by up to 2x, so compare builds on one machine
  only; the history of earlier measurements is in git (`git log -p
  CLAUDE.md`). The critical path (Syntax → Typing metatheory → Validity →
  the algorithm) is nearly the whole build, so more than 4 jobs don't
  help; only faster files on that path do.
- Fast full check: `make -j4 vos && make -j4 vok` (129 s + 355 s = 484 s
  on the 2026-10-11 tree, against 876 s for its `make`; `vos` alone took 393 s
  before the `Proof using` pass).
  `vos` compiles every file's statements without its proofs; `vok` then
  checks every file's proofs against the `.vos` files, all files in
  parallel, so it is not bound by the critical path. To work on one file:
  `make -j4 vos`, then `coqc -Q theories DeLaM -vok <file>`. Neither
  replaces the final `make`. A section lemma's proof is skipped by `vos`
  only with a `Proof using` clause; `tools/proof-using FILE.v ...` adds
  Coq's suggested clauses (run it on a sectioned file that `make TIMED=1
  vos` shows taking nearly its full time).
- Profiling (tools are in `tools/`, each documents itself in its header):
  - `tools/build-profile [-j N] [--clean] [--profile] [--label L]`: a timed
    build (`make TIMING=1`) and its report in `_profile/L/report.txt`:
    wall time, total CPU, critical path, slowest files and proofs, plus a
    per-declaration snapshot `decls.tsv`. `--profile` also writes Coq's
    `-profile` traces (`*.v.prof.json.gz`, open in ui.perfetto.dev).
  - `tools/critpath.py [-j N]`: critical path, slack and a simulated wall
    time at -jN, from the `.v.timing` files; `--what-if FILE=SECONDS`
    shows what speeding up a file would buy.
  - `tools/proofs.py [FILE.v ...]`: slowest proofs, split into tactics and
    `Qed`; `--sentences` for single sentences, `--diff A.tsv B.tsv` to
    compare two `decls.tsv` snapshots.
  - `tools/ltacprof.py FILE.v LINE|NAME`: one proof's sentence times and
    Ltac profile, compiled from a cut copy against the built tree.
  - `tools/imports.py --path`: files that wait for imports they don't
    reference (a candidate to split, as `LevelEqDef` was).
  - `tools/depgraph.py FILE.v`: FILE's declarations grouped by the
    latest module each needs, and its longest chain of declarations
    using one another (what is left of it if its independent parts built
    in parallel). `--try FILE=A,B` simulates a changed `Require` (and
    what its users then have to require); `--ideal` the build with
    every file requiring only what it references.
  - Inside a proof: `time "tag" tac`, or `Set Ltac Profiling.` …
    `Show Ltac Profile CutOff 2.` in a scratch copy.
  The build-time gotchas in `M1_DESIGN.md` list the patterns that made
  proofs slow; check new proofs against them.
- **Require what a file uses, not the latest file of its chain.** The
  dependency graph is the build's parallelism: a file requiring the
  last file before it waits for everything in between. The Validity
  per-former files (`Pi` … `WfElim`) each require only the formers they
  use, and wide files are split into parts that build in parallel
  (`LevelEq*`, `AlgDec*`, `GRenSyntax`, `RecReductCases`), with the old
  name kept as the file that exports them. The `.glob` misses names used
  only inside `Ltac`, hints and instances, so check a trimmed `Require`
  by compiling (and qualify a lemma name two modules share, as
  `SubstCommute.liftshift_single_ty` is in `AlgPrereq`).
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
