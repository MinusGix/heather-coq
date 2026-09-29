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
| `Id`, `refl`, `J` | positive, propositional | ext §5 | MX §6 | Id at `□` types observes code conversion; funext must stay propositional (MX §6 audit) | — |
| `Σ`, `pair`, `fst`/`snd` | negative, **η** | ext §6, §11.1 | MX §3 | surjective pairing is a genuinely new equation, not a congruence | **done** (M8a, M8d): every layer but V, β/η at D and M, recursor branches 13, 15–18 |
| `Unit^l` | **η = proof irrelevance** | ext §7, §11.2 | MX §4 | level-indexed (see findings) | **done** (M8c, M8d): as Σ; η as proof irrelevance; branches 14, 19, 20 |
| `Empty^l`, `elim_Empty` | positive, no β | ext §7 | MX §2 | Empty-η still open (`issues/empty-eta-conversion.md`) | — |
| `+`, `inl`/`inr`, `case` | positive | ext §8 | MX §2 | — | — |
| `W`, `sup`, `elim_W` | positive, infinitary | ext §9 | MX §5 | β builds an ih λ; the heaviest LR case | — |
| `Vec`, `Fin` | computing wrappers (reduce to Σ/Unit, +/Empty) | DESIGN.md | MX §10 | first type formers whose whnf is chosen by a term | — |
| `Wf`, `sup_f`, `elim_Wf` | finitary W over a `Vec` of children | wf-former-design | MX §11–17 | index lemma (MX §13) | — |
| `sEq`, `srefl`, `transp`, strip rule | strict equality, irrelevance | sprop-design | MX §18–22 | strip changes the evaluation notion; MX §19.4 substitution lemma is the named weak spot; completeness gap reaches type relations (MX §22.4) | — |
| `sEmpty`, `elim_sEmpty` | irrelevant empty type | sprop-design | MX §18, §21.4 | — | — |
| `Squash`, `ind_∥∥` | normalizing-total irrelevance | MX §27 | sketch only | full pass open (`issues/metatheory-ch07-squash.md`) | — |
| Bodied globals `u := t`, δ at p/m only | not a former | DESIGN.md, MX §23–25 | **none** | ch. 07 bill (`issues/metatheory-ch07-definitions.md`) | **done** (M9): occurrences carry their body (`gdef`); δ as reduction; §26 items 1–4; canonicity at D |
| `NatLit`, evaluator accelerations | representation | DESIGN.md | n/a | claimed to have no semantic content; nothing to prove here | out of scope |

Code recursor: the paper has 13 branches (indexed 0–12), Heather has 52.
Ours has 21 since M8d (`Typing/RecSpec.v`): Heather's Σ and Unit branches
are 13–20, in Heather's order, and later ones append after them. The declarative telescopes for ten of the new
recursive-call slots (`Vec`/`Wf`/`sEq`/`sEmpty` branches) are written
nowhere outside the kernel (`issues/uncovered-formers-recursor-rules.md`).
Transcribing those is where an error would go unnoticed on both sides, so
derive them from the semantics here rather than copying `rec.rs`.

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
  many types and breaks the recursor. Our Preservation lemma is the check
  when `Vec` lands.
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
  for global contexts with definitions; at D it holds. This bears on
  `issues/opaque-globals-analysis.md`. Loose ends (a checked witness of
  the M failure, N1's admissibility, consistency with definitions) are
  listed under M9_DESIGN.md, Open items.

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
4. `sEq`/`transp` and the strip rule: M10_DESIGN.md. M10a (`sEq`, `srefl`,
   `sEmpty`, irrelevance) has no fork; `transp` waits on S3, since MX §19.2's
   proposition turns out to be a strengthening lemma (S1).
5. The rest (Id, Empty, +, W, Vec/Fin/Wf, sEmpty, Squash).

Side task, any time: the ITree depth-indexed bisimilarity question.
