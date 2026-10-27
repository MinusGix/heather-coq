# DeLaM formalization: notes for agents

Start by reading `README.md` (status, milestone by milestone), then
`HEATHER.md` (Heather's extensions: the forward agenda),
`docs/design/M18_DESIGN.md` (the current milestone; M18b done, M18c next) and
`docs/gotchas.md` (proof-engineering and build-time gotchas; follow
them).

The design notes of the finished milestones, `M1_DESIGN.md` to
`M17_DESIGN.md`, are in `docs/design/` with `ELIM_CONGRUENCE.md` (typed
eliminator congruence) and `SYNTAX_SPIKE.md` (why the syntax is
hand-written). They record each former's decisions, deviations from the
paper and outcome; read the one for a former before changing it.
`M1_DESIGN.md` holds the shape decisions and the deviations from the
paper that every later milestone builds on. Comments in the theories cite
these docs by bare file name.

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
  (the relation must be `Prop`-valued) and `docs/design/SYNTAX_SPIKE.md`
  (hand-written syntax, with the representation of local/global
  substitutions).

## Build

- `nix develop path:. --command make -j4` (Coq 8.20, Equations, smpl from
  the flake). A clean build takes 10 to 26 minutes, depending on the
  machine. Latest: `par:` in the typing inductions, `Print Assumptions`
  out of `make` and a computed `closed_brDecls` (2026-10-27) took 1063 s
  and 1045 s wall at -j4 (critical path 874 s and 875 s) on a 4-core
  cloud machine, against 1174 s (critical path 1009 s) for the tree
  before, run between them. Then `TemplateEq.geq` (substitution
  equations by computation) and `tmNth`/`tmDNth` sealed with `simpl
  never` took 1029 s and 1002 s (CPU 2737 s and 2595 s), back to back;
  then `gnorm` (reduction states by computation), `wnorm` by `cbv` and
  `br_side` off the judgments took 953 s against 961 s (critical path
  839 s and 822 s, CPU 2300 s and 2463 s), back to back. Their CPU was
  off the critical path, which now runs `SubstCommute` → `TypedDnf` →
  `RecWf` → the Typing metatheory → `RulesS` → `RecSIWf` →
  `RecReductCases`. The same machine took anywhere from 976 s to 1609 s for
  that tree over one day, so only back-to-back runs compare. The
  `.timing` files count the main process only: `par:`'s workers are
  not in the "CPU" total, and they slow the files built beside them
  (about 6% here).
  Machines differ by up to 2x, so compare builds on one machine
  only, back to back; the history of earlier measurements is in git
  (`git log -p CLAUDE.md`). The critical path (Syntax → Typing metatheory → Validity →
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
  The build-time gotchas in `docs/gotchas.md` list the patterns that made
  proofs slow; check new proofs against them.
- **Require what a file uses, not the latest file of its chain.** The
  dependency graph is the build's parallelism: a file requiring the
  last file before it waits for everything in between. The Validity
  per-former files (`Pi` … `WfElim`) each require only the formers they
  use, and wide files are split into parts that build in parallel
  (`LevelEq*`, `AlgDec*`, `GRenSyntax`, `RecReductCases`, `RecS*`,
  `RecWfBase`),
  with the old name kept as the file that exports them. A metatheory
  file's syntactic lemmas (commutations, the recursors' data under an
  operation, untyped reductions) and its per-former lemmas go in a file
  of their own that requires only what they use (`ReductionBase`,
  `GRenRec`, `SubstRec`, `WfNthReds`, `PresupAux`); `tools/depgraph.py FILE.v --decls` lists each
  declaration's latest needed module. A sectioned
  file splits by bundling its hypotheses into a class, as `RecS` does
  (`RecSBase.v`; the recipe is in `docs/gotchas.md`'s build-time
  gotchas): a new former's recursion cases go in the `RecS*` part of
  its group, its `RT_*`/`Rt_*` lemma and `rec_code` case in `RecS`. The `.glob` misses names used
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
