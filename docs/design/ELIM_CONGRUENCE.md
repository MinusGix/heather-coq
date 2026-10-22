# Typed eliminator congruence, design

Status: **done** (2026-10-16; `elim_IWf`'s induction-hypothesis types
dropped too, 2026-10-20). Why: Heather's
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
| `elim_IWf` | motive level `l' ≤≥ k'`, `M`, step `c`     | `l`, `li`, `X`, `A`, `N`, `Ot`, `C`, the index `m`, the IH types |

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

- **The motive.** Two eliminations of the same scrutinee may differ in
  their motives, so `M ≅ M'` stays.
- **The branches / steps** (`c`, `c1`, `c2`).
- **The motive's level** stays compared, although it is redundant in the
  declarative theory: `M ≅ M' @ l'` gives `M' @ l'` (presupposition), and
  with the right elimination's `M' @ k'` level uniqueness (`ty_lvl_uniq`)
  gives `l' ≡ k'`. The algorithm cannot use that argument as it stands.
  Soundness of `ac_ty` (`S_ty`, `AlgSound.v`) holds for two types at
  *one* level, and the rule's soundness moves the right motive into the
  left telescope at the left level along `l' ≡ k'` (`IWf_mot_left` and
  its siblings) *before* the motives' comparison can be read
  declaratively. Without the level premise that step would need a
  level-heterogeneous soundness (algorithmically convertible types, well
  typed at `k` and `k'`, have `k ≡ k'`), a new induction over all of
  `ac_ty`. The check is one level comparison, which costs nothing next to
  a type, so dropping it is not free and not worth it: it stays. For
  Heather the same holds: the kernel may skip it in theory, but it is
  the cheapest premise of the rule.

## `elim_IWf`'s induction-hypothesis types (2026-10-20)

Until 2026-10-20 the algorithmic `actmne_elimIWf` compared the two
induction-hypothesis types (`ac_ty` at `iwfihty`), mirroring
`eqtm_elimIWf`'s admissible premise (M17_DESIGN.md, "Two admissible
premises"). It no longer does: the equation is a consequence of the
signatures' equation, which the scrutinee forces, and the motives'.

`iwfihty` is `Π(i : Fin N). M[C, dnth(N; k. IWf(…)(C); cs; i)]` at either
signature: the domains are `Fin` at the arities, and the codomains are the
motives at the child indices and at two `dnth`s whose length and family
(and level) differ. The congruence of `dnth` over its annotations needed no
new proof: `dnth`'s index lemma `V_dnth` (M17a, `DVecNth.v`) is already
relational (`dnth` at related lengths, families, tuples and indices gives
related results), and `elimIWf_Vdnth` (`IWfElim.v`) instantiates it at the
children's tuple. `Validity/IWfIhEq.v` composes it:

- `VG_iwfihty`: the two induction-hypothesis types are valid against each
  other, from the signatures' and the motives' validity: `Π`'s validity,
  `Fin`'s at the arities, and the motive's validity instantiated at the
  child indices and the `dnth`s (`VG_wk3_s2`, a type under two binders
  weakened past three entries and instantiated at related terms).
- `decl_IWf_ihty_eq` (P) and `declM_IWf_ihty_eq` (M): the fundamental
  theorem turns the declarative premises into validity, at the identity
  global substitution (`VTyS_gid`, `VTmS_gid`); `VG_iwfihty` relates the
  two types; escape (`escape_ty`, `geq_ty_sound`) gives the declarative
  equation (`IWf_ihty_geq`, generic in the instance).
- `IWf_ihty_eq`: the two together at any computing layer, from `IWfEq`,
  `l' ≡ k'`, `M ≅ M'` and the right type's typing in the left telescope,
  which is what every use site has (`IWf_ih_left`).

**The declarative `eqtm_elimIWf` keeps its premise.** The lemma goes
through the fundamental theorem, whose proof is an induction over the
declarative derivations and so cannot use it for the rule itself, nor can
presupposition, substitution and the other metatheory before it. And the
rule holds at layer C too, where there is no logical relation to derive
the equation from (`fundamentalS_le` lifts a layer-C derivation to P, but
an equation at P does not come back down to C). The premise stays
admissible at P and M, now provably so (`IWf_ihty_eq`).

For Heather: the kernel's `elim_IWf` neutral arm may skip the
induction-hypothesis types as well, so it compares the scrutinees as
neutrals, the motive's level, the motive and the step only.

## Soundness, completeness, decidability

All re-proved, no admits or axioms added (`Print Assumptions` on
`wf_tm_dec` and `infer_dec`, `TypeCheck.v`: closed under the global
context; full `make` green, 2026-10-16, and again on 2026-10-20 after the
induction-hypothesis types were dropped):

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
- `elim_IWf`'s induction-hypothesis types (2026-10-20): soundness,
  completeness, symmetry, transitivity and decidability take the equation
  the step's telescope conversion needs from `IWf_ihty_eq` instead of the
  dropped comparison (for transitivity, once per pair: `1–2`, `2–3`,
  `1–3`).

`natrec`/`elim_Nat` and the irrelevant eliminators (`elimEmpty`,
`elimSEmpty`, `ind_∥∥`) are untouched: `Nat` has no annotations to drop,
and the irrelevant ones never compare their scrutinees.
