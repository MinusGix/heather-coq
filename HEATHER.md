# Heather: what its kernel adds to DeLaM, and what we check

Heather (`~/Kairos/Code/heather`, written `H/` below; from this repo,
`../../heather`) is a theorem-prover language whose Rust kernel implements
the full four-layer DeLaM of ch. 04 plus extensions of its own. Not to be
confused with `../heather`, the early Lean λΠ attempt that only holds the
paper sources (`../heather/docs/delam/*.tex`).

The kernel says it "mirrors the in-progress Coq formalization of DeLaM",
i.e. this repo. Its extensions are specified in prose and checked on paper
only. This document tracks those pieces, what Heather already knows about
them, and how far we have machine-checked them.

Surveyed at Heather `02c692bf` (2026-09-27).

## Direction of authority

- We transcribe Heather's declarative rules and prove them here. Heather's
  rules are a proposal, not scripture. Where we find a rule that is odd, or
  a clearly better formulation, we change Heather, not only our copy.
- A derivation of `False` (or of a failure of canonicity, decidability or
  subject reduction) in a transcribed rule set is a Heather soundness bug.
  File it in `H/issues/` with the Coq witness.
- Rule choices that are ours alone (as in M1–M7) are recorded here, marked
  as departures from Heather, with the reason.

## Where Heather keeps things

| What | Where |
|---|---|
| Kernel design, per-extension rationale | `H/crates/kernel/DESIGN.md` (§Fragment) |
| Declarative rules for Id, Σ, Unit/Empty, +, W, the recursor β schema | `H/docs/delam-extensions.md` |
| Paper passes of ch. 07 for every extension | `H/docs/metatheory-ch07-extensions.md` (Parts I–IV, §27) |
| SProp / `sEq` / Squash design | `H/docs/sprop-design.md` |
| `Wf` former design | `H/docs/wf-former-design.md` |
| Audit of the 53 ch. 05/06 lemmas vs the kernel | `H/docs/ch05-06-lemma-audit.md` |
| Interaction trees investigation | `H/docs/interaction-trees-fit.md` |
| Issue tracker | `H/issues/*.md` (`H/scripts/issue`) |
| Kernel source: typing, reduction, recursor telescopes | `H/crates/kernel/src/{typing,reduce,rec,term,conv}.rs` |

## The pieces

"Paper pass" is the section of `metatheory-ch07-extensions.md` (`MX` below)
that checks the ch. 07 obligations by hand. "Ours" is the status here.

| Piece | Kind | Heather rules | Paper pass | Known concerns | Ours |
|---|---|---|---|---|---|
| `Id`, `refl`, `J` | positive, propositional | ext §5 | MX §6 | Id at `□` types observes code conversion; funext must stay propositional (MX §6 audit) | **M11 done**: every layer but V, β and no η at D/M, canonicity, code, four recursor branches |
| `Σ`, `pair`, `fst`/`snd` | negative, **η** | ext §6, §11.1 | MX §3 | surjective pairing is a genuinely new equation, not a congruence | **done** (M8a, M8d): every layer but V, β/η at D and M, recursor branches 13, 15–18 |
| `Unit^l` | **η = proof irrelevance** | ext §7, §11.2 | MX §4 | level-indexed (see findings) | **done** (M8c, M8d): as Σ; η as proof irrelevance; branches 14, 19, 20 |
| `Empty^l`, `elim_Empty` | positive, no β; η = proof irrelevance | ext §7 | MX §2 | Empty-η was open (`issues/empty-eta-conversion.md`); settled here, see `M12_DESIGN.md` last section | **done** (M12a; every layer but V with code and branches 31–33, M12c): no closed term (`closed_empty_empty`); proof irrelevance at D and M (2026-10-06) |
| `+`, `inl`/`inr`, `case` | positive | ext §8 | MX §2 | — | **done** (M12b; every layer but V with code and branches 34–38, M12c): β at D and M, no η, disjunction property (`closed_sum_canonicity`) |
| `W`, `sup`, `elim_W` | positive, infinitary | ext §9 | MX §5 | β builds an ih λ; the heaviest LR case | **M13 done**: β, no η, `closed_W_canonicity` (M13a, D and M); code, lift to C and the four branches (M13b) |
| `Vec`, `Fin` | computing wrappers (reduce to Σ/Unit, +/Empty) | DESIGN.md | MX §10 | first type formers whose whnf is chosen by a term | **M14 done**: no LR case, validity by induction on the length; preservation at `Vec^l(A;0) ⇝ Unit^l` (M14a, D and M); codes, every layer but V, branches 43–46 (M14b) |
| `Wf`, `sup_f`, `elim_Wf` | finitary W over a `Vec` of children | wf-former-design | MX §11–17 | index lemma (MX §13) | **M15 done**: branch telescopes derived from the semantics, β, no η, the index lemma via `nth` at related `Fin` indices (M15a, D and M); code, every layer but V, branches 47–50 (M15b) |
| `sEq`, `srefl`, `transp`, strip rule | strict equality, irrelevance | sprop-design | MX §18–22 | strip changes the evaluation notion; MX §19.4 substitution lemma is the named weak spot; completeness gap reaches type relations (MX §22.4); **MX §19.2 is a strengthening lemma (M10 S1)** | `sEq`, `srefl`, irrelevance **done** (M10a; every layer but V with codes and branches 25, 26, 29, M10c); `transp` removed (S8) |
| `sEmpty`, `elim_sEmpty` | irrelevant empty type | sprop-design | MX §18, §21.4 | — | **done** (M10a; at code with branches 27, 28, 30, M10c) |
| `Squash`, `ind_∥∥` | normalizing-total irrelevance | MX §27 | sketch only | full pass open (`issues/metatheory-ch07-squash.md`); the payload must be self-related (see findings) | **done** (M16a at D and M: the probe's relation (`probes/SquashProbe.v`), proof irrelevance, β, no η, canonicity to a `squash`; M16b: code `∥s∥`, every layer but V, branches 51–54) |
| Bodied globals `u := t`, δ at p/m only | not a former | DESIGN.md, MX §23–25 | **none** | ch. 07 bill (`issues/metatheory-ch07-definitions.md`) | **done** (M9): occurrences carry their body (`gdef`); δ as reduction; §26 items 1–4; canonicity at D; consistency at D and M |
| `NatLit`, evaluator accelerations | representation | DESIGN.md | n/a | claimed to have no semantic content; nothing to prove here | out of scope |

Code recursor: the paper has 13 branches (indexed 0–12), Heather has 52.
Ours has 47 (`Typing/RecSpec.v`): Heather's Σ and Unit branches are 13–20
(M8d), `Id` 21–24 (M11b), `sEq`/`sEmpty` 25–30 (M10c), `Empty` and `+`
31–38 (M12c), `W` 39–42 (M13b), `Vec` and `Fin` 43–46 (M14b), each group
in Heather's order, appended as they came. The declarative telescopes for ten of the new
recursive-call slots (`Vec`/`Wf`/`sEq`/`sEmpty` branches) are written
nowhere outside the kernel (`issues/uncovered-formers-recursor-rules.md`).
Transcribing those is where an error would go unnoticed on both sides, so
derive them from the semantics here rather than copying `rec.rs`. `Vec`'s
slot (`ty_vec`'s length call, at the term motive) is now derived and
validated here and agrees with `rec.rs` (M14_DESIGN.md).

## Findings

Cross-checks between the two sides, newest last.

- **`t_elimN` scrutinee level (paper typo).** Heather found that ch. 04
  declares the recursive call on the natrec branch's scrutinee at the
  motive's level `ℓ` instead of `0`
  (`issues/recursor-elim-call-level-mismatch.md`). Ours already has level
  0 (`Typing/RecSpec.v:136`), and the M3 fundamental theorem covers it.
  Nothing to do.
- **`Vec^l(T;0) ⇝ Unit` dropped a level**, breaking type-level Preservation.
  Heather fixed it by level-indexing `Unit^l`/`Empty^l`
  (`issues/unit-level-and-vec-preservation.md`, closed). Making them
  level-polymorphic instead was tried and reverted: it gives `box Unit`
  many types and breaks the recursor. Checked at M14a: `RS_vec_zero`
  preserves `Vec^l(A;0)`'s type at the same level `l`
  (M14_DESIGN.md).
- **Σ and Unit (M8).** Heather's rules went through as written: the
  formers at every layer but V, the computation rules (β, η, the codes'
  decodings) at D and M only. Two additions of ours, neither a change to
  Heather: `eqtm_triv`, the congruence of `⟨⟩` over level-equivalent
  annotations, which Heather does not need (it has no level-equivalence
  relation on code; ours is M3_DESIGN.md E11) and which at D and M follows
  from η; and the relation for Unit keeps weak-head normal forms (M8_DESIGN.md
  K5), a semantic choice with no rule behind it.
- **Bodied globals (M9).** Heather's rules went through, with a recorded
  syntactic departure: an occurrence of a defined `u` is `gdef u t δ`,
  carrying the body, so reduction stays context-free (M9_DESIGN.md (b)).
  The ch. 07 bill of `issues/metatheory-ch07-definitions.md` is paid:
  glueing is anti-reduction plus the body's validity, coherence across `□`
  is structural, and no valid-global-context induction is needed, because
  the use rule carries the body's typing at the use layer (N1). A second
  addition: the carried body is the declared one up to level equivalence
  (N2), forced by our Static Code lemma. One consequence for Heather's
  design: since `elim(box(u^δ))` stays stuck, closed canonicity at M fails
  for global contexts with definitions (checked instance:
  `Validity/DefStuck.v`); at D it holds. Consistency holds at both D and M
  (`Validity/ConsistencyDef.v`), by unfolding every definition, code
  included, which preserves every judgment. This bears on
  `issues/opaque-globals-analysis.md`. Loose ends (N1's admissibility, a
  Heather-faithful rule set) are listed under M9_DESIGN.md, Open items.
- **Squash's relation (probe, 2026-10-08).** MX §27's "normalizing-total"
  clause needs one refinement, and is otherwise not new here.
  `probes/SquashProbe.v` states the clause over the development's LR, with
  `∥·∥` and `squash` as section variables and two generic laws (congruence,
  proof irrelevance) as hypotheses, satisfiable by `Unit`
  (`Squash_hyps_unit`). Findings:
  - *The payload must be related to itself.* A whnf at `∥A∥` is good when
    it is `squash a` with `RA a a`, or a neutral `ν ~ ν`; `t ~ t'` is "both
    good", a product of two unary predicates. §27 asks for no relation on
    payloads at all, but `ind(squash a; z.B; x.b) ⤳ b[a/x]` instantiates
    `b`'s validity at `a`, which needs `a` in `A`'s relation; typing alone
    does not give it. Nothing is compared across the two sides, so the
    algorithm (both sides to whnf, then accept) is unaffected, and so is
    Heather's `conv.rs`.
  - *Normalization is already required at Unit and sEq here.* `UnitRel`
    and `SEqRel` keep both sides' whnfs (M8_DESIGN.md K5), so the property
    §27 calls new is the existing shape. The clause is `Empty`'s
    self-related shape with `+`'s kept carrier relation.
  - *Abort criterion not met.* PER laws, escape for types and terms,
    symmetry and reflexivity of the type clause from the carrier's, change
    of carrier (reading only the diagonal of `RA`), irrelevance of the
    derivation, and weak-head expansion all go through without relevance
    marks or a new sort. The shared syntactic lemmas see `squash` as an
    ordinary constructor.
  - *Size of a full round.* At D and M, between M12a and M12b (about 55
    files, 1500 to 2000 lines): one carrier as `+`, one constructor, a
    dependent eliminator whose step has type `∥B(squash x)∥`, and the
    irrelevance arm as at `sEq`. Codes and Heather's four recursor
    branches (`ty_squash`, `tm_squash`, `tm_squash_in`, `tm_elim_squash`)
    as half of M12c (about 30 files, 1000 to 1300 lines).

## Beyond type formers

- **Interaction trees.** `issues/interaction-trees-container-model.md`
  Q1: for deterministic trees, does depth-indexed bisimilarity
  (`∀ n. euttₙ`) coincide with the coinductive one? A standalone Coq
  question, independent of DeLaM. Heather's route (container events,
  fuel-cut trees, no kernel coinduction) depends on it.
- **Coinduction and layering.** `issues/effects-direction.md` asks this
  repo whether layering tolerates kernel coinduction. Heather's current
  answer avoids needing it.
- **Lemma sweep.** `issues/metatheory-lemma-sweep.md` property-tests the
  ch. 05/06 lemmas against the kernel. For the paper's fragment we prove
  them; we can point that issue's audit at our statements.
- **Multimodal type theory.** `issues/multimodal-modalities.md` asks
  whether DeLaM's layers are an MTT mode theory. Research, not scheduled.
- **Globals in code analysis.** `issues/opaque-globals-analysis.md`:
  recursor branch for `u^δ` versus unfolding for analysis. It interacts
  with the definitions round and with ch. 07's stuck laws.

## Making this repo easier to extend

One former currently touches 40–60 of our files (`natrec` 40 files,
`tyPi` 61, `letboxt` 30, by `grep -lw`). Most of those touches are
per-constructor boilerplate: renaming, the three substitutions and their
commutation, weakening, inversion, congruence rules, reduction,
presupposition, the recursor telescope, and the generic-equivalence laws.
Heather's list would multiply that by roughly twelve.

Candidate directions. Each is a design fork to discuss when we reach it:

1. **Derive recursor branches from constructor signatures.** A branch's
   telescope (universe binders, global bindings, recursive calls) follows
   from the constructor's argument sorts and levels. Heather's own level
   bug and its ten unattested slots are the argument for this. It needs a
   first-class description of each constructor's argument shape.
2. **A binding signature for the local part of the syntax.** SYNTAX_SPIKE
   ruled out Autosubst for the global/code parts (stored substitutions,
   separate code scopes). A signature covering only the ordinary local
   formers, with the modal constructors still hand-written, could generate
   renaming, substitution and commutation lemmas.
3. **Tactic-level genericity.** Keep the syntax as it is and push more of
   the per-constructor cases into `smpl`-driven automation, so a new
   constructor mostly adds hint entries.

Plan: add Σ (with η) and Unit (with η) by hand first, record which files
each one touched and why, then choose among 1–3 using that data.

**Direction 1, decided 2026-10-09: the narrow version, as M15b's step 0.**
Measured on M11b–M14b, branch-specific code is ~525–1360 lines per
code-and-branches round, about 15–20% of a former; the D/M rounds' logical
relation dominates. Checked in Coq: for all 47 branches, `br_calls` and
`br_nl` follow exactly from `brDecls` (one call per layer-C global,
weakened past its position), so the call table is redundant; heads and
reducts need the constructor and stay hand-written. Step 0 derives
`br_calls` from `brDecls`, adds a generic `GS_br` fold over `brDecls`, a
per-call lemma (what `Tcall`/`tcall` and the `X1r` lines do), and a tactic
for `RT_`/`Rt_`, all used first on Wf's branches. The existing branches are
not migrated. Abort, and hand-write as M13b did, if Wf's RecS plus
RecReduct is not under about 60% of W's (794 lines) or the build slows.
Not done: deriving `redT`/`redt` from one descriptor (M8 J2's reasons
still hold: it redefines `redT`, used in 17 files, to save ~10–20 lines
per branch).

**Outcome (M15b, 2026-10-10): kept, at the threshold.** Wf's
branch-specific `RecS` plus `RecReduct` code is about 500 lines (`RecS`
about 350, `RecReduct` about 150), about 63% of W's 794: on the abort line
rather than under it. The generic part it bought is about 200 more lines
and serves any later group of branches: `GSall`/`GS_br` (and
`GWall`/`GW_br` in `RecReduct`), `RTcall`/`Rtcall`, the `gs_solve` and
`gw_solve` tactics. Kept rather than redone by hand, since hand-writing
would have been W's size again. What changed from the plan:
- `br_calls` stays a written table, checked against the derived one
  (`br_calls_derived`, all 51 branches by `vm_compute`): a computed table
  normalizes `elim_Wf`'s step telescope past its notations, which the
  branch proofs rewrite with.
- The `RT_`/`Rt_` tactic is subsumed: with `RTcall`/`Rtcall` doing each
  call's work, a branch is one lemma (`RT_wf`, `Rt_codewf`, `Rt_supf`,
  `Rt_elimWf`) that applies `rec_T_br`/`rec_t_br` to two `GS_br` folds
  and discharges the bullets by small tactics, so no tactic over the
  bullets was worth writing.
- Perf trap: a `gs_solve` that rewrote each scope declaration with
  `replace` cost 26 s per call; normalizing the images (`gs_norm`) and
  closing by `assumption` is under a second.
On the other criterion, the build did slow (critical path +12% on one
machine), but the generic layer is about 2 s of it; the rest is the four
branches themselves (branch 50's `nth`-carrying step scope above all),
which hand-written branches would pay too. Details in M15_DESIGN.md's
M15b outcome.

## Proposed order

1. ~~Σ with η, Unit with η: the two new equations; measure the per-former cost.~~
   Done (M8a–M8d).
2. ~~Decide the genericity direction from that measurement.~~ Done: shared
   generic laws and algorithmic families (M8_DESIGN.md J1), recursor branches
   through one generic lemma per side (J2), shared call and binder bodies (L4).
   Rule lists: a rule with ordinary premises needs no entry in the
   metatheory dispatch (M8_DESIGN.md L5).
3. ~~Bodied globals with layer-indexed δ: the one piece with no paper pass.~~
   Done (M9).
4. ~~`sEq`/`transp` and the strip rule~~ Closed at M10a (M10_DESIGN.md):
   Heather removed `transp` and the strip (S8). M10c, the codes (six
   branches, no `transp`), is done. Indexed families become the `IWf`
   former (H `docs/iwf-former-design.md`), a milestone after `W`/`Wf`.
   Its rule set (§1–§6) was frozen on 2026-10-13. `Vec`/`Wf` stay separate
   formers in Heather for now, with abbreviations as the target (its §10),
   so `DVec`/`IWf` land here as siblings of `Vec`/`Wf`. The two pairs are
   translations, not conversions: at a neutral length they are distinct
   neutral types, and `elim_IWf`'s ih goes through `dnth` where
   `elim_Wf`'s goes through `nth`. The relation probe checks `dnth`'s
   index lemma first: the ih's type is `F[i]` only up to β, one step more
   than `V_nth` (M15a) needed.
5. The rest (Id, Empty, +, W, Vec/Fin/Wf, sEmpty, Squash). `Id` is done (M11a and
   M11b, M11_DESIGN.md). `Empty` and `+` are done, with codes and
   recursor branches (M12a–c, M12_DESIGN.md). `W` is done, with its
   code and four recursor branches (M13a–b, M13_DESIGN.md). `Vec` and
   `Fin` are done, with codes and four recursor branches (M14a–b,
   M14_DESIGN.md). `Wf` is done, with its code and four recursor branches
   (M15a–b, M15_DESIGN.md). `Squash` is done, with its code and four
   recursor branches (M16a–b, M16_DESIGN.md).

Side task, any time: the ITree depth-indexed bisimilarity question.
