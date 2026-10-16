# Typed eliminator congruence, design

Status: **done** (2026-10-16). Why: Heather's
`H/issues/conversion-typed-eliminator-congruence.md` asks conversion to stop
re-comparing, at every meeting of two neutral eliminations, the annotations
that the scrutinee's type already determines. `actmne_fst`/`actmne_snd`
already worked this way here (they compare the scrutinees and read the
components off the inferred Σ). This note extends the same treatment to
`J`, `case`, `elim_W`, `elim_Wf` and `elim_IWf`, and records which
components turned out to be forced, levels included, and which did not.

## The rules

Each eliminator's neutral rule in `Typing/Algorithmic.v` now has, as
premises, only:

| eliminator | compared                                  | no longer compared (forced)       |
|------------|-------------------------------------------|-----------------------------------|
| `J`        | motive level `l2 ≤≥ l4`, motive `M`, base `c` | `l1`, `A`, `a`, `u`           |
| `case`     | motive level `l3 ≤≥ l6`, `M`, `c1`, `c2`  | `l1`, `l2`, `A`, `B`              |
| `elim_W`   | motive level `l3 ≤≥ l6`, `M`, step `c`    | `l1`, `l2`, `A`, `B`              |
| `elim_Wf`  | motive level `l2 ≤≥ l4`, `M`, step `c`    | `l1`, `A`, `N`                    |
| `elim_IWf` | motive level `l' ≤≥ k'`, `M`, the IH types, step `c` | `l`, `li`, `X`, `A`, `N`, `Ot`, `C`, the index `m` |

plus, in every case, the scrutinees as neutrals (`ac_tmnee G Γ ν ν' W`),
where `W` is left free: it is whatever whnf the scrutinee comparison
infers, and nothing in the rule matches on it.

**Every forced annotation is forced with its level.** The scrutinee
comparison gives, by soundness, `T ≅ W @ k` and `T' ≅ W @ k'`, where
`T`, `T'` are the two eliminations' annotated scrutinee types (`Id l1 A a
u`, `Σ+ l1 l2 A B`, …) and `k`, `k'` their levels. A type's level is unique
up to equivalence (`ty_lvl_uniq`), so `k ≡ k'` and `T ≅ T'` (`eqty_meet`,
`AlgSound.v`); the formers' injectivity (`id_inj_c`, `sum_inj_c`,
`W_inj_c`, `Wf_inj_c`, `IWf_inj_c`) then splits that into the components
and their levels one by one (`J_annots`, `case_annots`, `W_annots`,
`Wf_annots`, `IWf_annots`). Nothing about the levels needed an extra
argument: for `Σ+` and `W` only `lmax l1 l2 ≡ lmax l4 l5` comes out of
uniqueness, and the per-component equivalences come from injectivity,
which states them.

**The motives and branches are compared in the left elimination's
telescope** (`Γ ,, A @ l1 ,, Id …` for `J`, and so on), not in a telescope
read off `W`. Heather's issue words it as "at the inferred telescope"; the
two are the same judgement, because the left telescope is convertible to
the inferred one (the equalities above, then context conversion, `cv_ty`
and the per-former context lemmas such as `J_ctx_conv`). The left one was
chosen because it needs no read of `W` at all, so the rule does not have
to reduce or invert `W`, and the proofs reuse the bridges that already
existed. An implementation is free to use either.

## What is not forced

- **The motive and its level.** Two eliminations of the same scrutinee
  may differ in their motives, so `M ≅ M'` stays. The motive's level is
  likewise not a component of the scrutinee's type, so `leqv` on it stays.
  (It is probably redundant given `M ≅ M'` and level uniqueness, as the
  scrutinee's level is; that is not checked here, and the check is a
  level comparison, which costs nothing next to a type.)
- **The branches / steps** (`c`, `c1`, `c2`).
- **`elim_IWf`'s induction hypothesis types.** The declarative
  `eqtm_elimIWf` states `iwfihty(left) ≅ iwfihty(right)` as a premise, one
  of M17's two admissible premises (M17_DESIGN.md, "Two admissible
  premises"), because `dnth`'s typing comes after presupposition. The
  algorithmic rule mirrors it, and the right IH type is built from the
  right signature, so the right `X'`, `A'`, `N'`, `Ot'`, `C'` are still
  traversed there, inside `dnth`'s annotations. The premise follows from
  the motives' and signatures' equality once a `dnth` congruence over its
  annotations is in the tree; with it, the rule could drop the IH types
  too. That lemma is not here, so the claim is inferred, not checked.
  For Heather: the IH-type comparison is semantically redundant (it is a
  consequence of the signature equality the scrutinee forces and `M ≅
  M'`), but this tree does not prove it.

## Soundness, completeness, decidability

All re-proved, no admits or axioms added (`Print Assumptions` on
`wf_tm_dec` and `infer_dec`, `TypeCheck.v`: closed under the global
context; full `make` green, 2026-10-16):

- Soundness (`S_actmne_*`, `AlgSound.v`): the annotations come from the
  scrutinee's IH via `*_annots`, then the existing declarative congruence
  `eqtm_J`, `eqtm_case`, … applies as before.
- Completeness (`C_actmne_*`, `AlgConv.v`): the forced premises are no
  longer produced, so the cases lost their IH bullets; the left telescope's
  conversion to the right one now comes from the scrutinee's soundness
  (`ac_nee_sound'`) instead of the annotation comparison.
- Symmetry and transitivity (`Y_actmne_*`, `T_actmne_*`, `AlgPER.v`): the
  motive and branch IHs live in the left telescope; flipping or chaining
  needs the telescopes' conversion, which comes from the scrutinee
  derivations (both for symmetry; `1–2` and `2–3`, chained by
  `eqty_chain`, for transitivity) instead of the dropped premises.
- Decidability (`Dc_actmne_*`, `AlgDecCode.v`, `AlgDecW.v`,
  `AlgDecIWf.v`): decide the scrutinees first, then read the telescope
  conversion off the result as completeness does, and decide only the
  motive level, motive and branches.
- Inversions `ainv_J`, `ainv_case`, `ainv_elimW`, `ainv_elimWf`,
  `ainv_elimIWf` shrank with the rules; `AlgInstance.v` builds the shorter
  rules; `AlgStruct.v` (weakening, level-leq) needed no change.

`natrec`/`elim_Nat` and the irrelevant eliminators (`elimEmpty`,
`elimSEmpty`, `ind_∥∥`) are untouched: `Nat` has no annotations to drop,
and the irrelevant ones never compare their scrutinees.
