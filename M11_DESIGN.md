# M11: the identity type (`Id`, `refl`, `J`), design

Status: **M11a and M11b done, 2026-09-30** (outcomes below). Why now: the no-UIP model
argument (Heather `docs/no-uip-model.md`) cannot be checked against this
development until it can state UIP, and that needs `Id`. It is also
`HEATHER.md` item 5's first former.

Heather's rules: `H/docs/delam-extensions.md` §5.
- Formation `Id^l(S; t; u) @ l`.
- `refl^l(S; t) : Id^l(S; t; t)`, with syntactically identical endpoints.
- Paulin-Mohring `J^{l,l'}(S; a; y p. M; c; u; e) : M[u/y, e/p]`. The left
  endpoint `a` is fixed. The motive binds `y : S` and
  `p : Id(S↑; a↑; y)`.
- β `J(S; a; y p. M; c; a; refl(S; a)) ≈ c`, at computing layers.
- No η: that is the absence of K.
- Congruences, with `refl`'s comparing only the points.
- Codes `Id^l(s; t; u) : Ty l`, and four code-recursor branches.

## Staging

**M11a: `Id`, `refl`, `J` at layers D and M, with no codes.** It is
M10a's scope and gating: every rule takes `compt i`, as `sEq`'s do, so the
code layer and the recursor branches wait for M11b.

- **Syntax**: `tyId l A a b`, `tmRefl l A a`, and `tmJ l l' A a M c u e`,
  with `M` under two binders (`y`, then `p`) and every operation's case.
- **Rules**:
  - formation;
  - `refl`;
  - `J`, whose motive context is `Γ ,, A ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0)`, and
    whose result type is `M[lsingle2 u e]`;
  - congruences of all three, with `refl`'s comparing the carrier and
    the point;
  - β in Heather's syntactic form.

  The general β (`J(…; u; refl(A'; a'))` with `u ≅ a`, `A' ≅ A`,
  `a' ≅ a`) is a derived lemma, by congruence. Typed reduction uses it
  with premises supplied by the relation.
- **Reduction**:
  - `J` reduces its proof position;
  - `J(…; refl …) ⇝ c`, untyped, ignoring the annotations, which is
    logrel-coq's `tIdElim … (tRefl …) ⇝ hr`;
  - `J` is `whne` on a `whne` proof;
  - `refl` is `whnf`.
- **Relation**, following logrel-coq's `Id`:
  - The type relation keeps the carrier's relation, not only generic
    equalities as `sEq`'s does (M10a). The term relation needs it.
  - The endpoints are related at the carrier.
  - Terms reduce to a weak-head normal form that is either `refl A' a'`
    with `A' ≅ A`, `a' ~ a'` and `a'` related to both endpoints at the
    carrier, or a neutral, related generically.
  - No `refl ~ neutral` case, because there is no η.
- **Fundamental theorem**, `J`'s case:
  - The proof is reducible at `Id`.
  - A `refl` whnf gives the typed β step, with the equalities read off
    the relation. The case term finishes it.
  - A neutral whnf makes `J` neutral, by a new generic law.
- **Algorithm**:
  - `refl` against `refl`: compare carriers and points.
  - `J` neutral against `J` neutral: compare carriers, left endpoints,
    motives in the extended context, cases, right endpoints and proofs.
  - No irrelevance arm.
- **Consequences**:
  - canonicity at `Id`: a closed proof computes to `refl`, and then its
    endpoints are convertible;
  - consistency is unchanged;
  - decidability and type checking extend.

**M11b: codes and the four recursor branches** (`t_Id`, `t'_Id`,
`t_refl`, `t_J`, H §5.8), after M11a.

Measure against M10a (1517 lines in 53 files) and M8c.

## M11a outcome (2026-09-30)

Done at layers D and M, gated by `compt i`, with no codes. Every headline
theorem (`consistency`, `closed_canonicity`, `tyd`, `ckd`, `ac_tm_dec`,
`decl_eqtm_dec_any`, `red_sound_tm`, `type_uniq`, and the M10a
corollaries) stays closed under the global context. The development can
now state UIP for `Id`.

- **Rules** (`Declarative.v`): `wft_id`, `wf_idrefl`, `wf_J`, `eqty_id`,
  `eqtm_idrefl`, `eqtm_J`, `eqtm_J_beta`. `J`'s rules also take the motive
  context's `Id` entry, `[Γ ,, A ⊢ tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l]`, as a
  premise. It is a presupposition premise (the recursors' M3 E10): the
  shifted entry only commutes with weakening and substitution up to an
  equation, so its induction hypothesis is what supplies the extended
  context under every operation. The general β (at `u ≅ a` and any `refl`
  of the `Id` type) is derived twice: generically at `⊢g`
  (`J_refl_eq`, `Validity/Id.v`) and declaratively (`RS_J_beta`,
  `Preservation.v`, via inversion and `Id` injectivity).
- **Relation** (`LRid`, `IdRel`, `IdNf`). As planned, following logrel-coq:
  - the carrier's relation is kept, at `Γ` (non-Kripke);
  - the endpoints are related at it;
  - `IdNf` has a `refl`/`refl` case and a neutral case, and no mixed case.

  Two deviations:
  - `LRid` stores the carrier relation's symmetry and transitivity, as
    logrel-coq's `tyPER`. Symmetry and transitivity at `Id` need them
    before they are proven for the carrier. `LR_tm_per`
    (`Transitivity.v`) supplies them when the relation is built.
  - The `refl` case records both annotation levels and the carriers'
    equality with the `Id` type's. `J`'s β reads them before `Id`
    injectivity exists.

  `Weakening.v`'s LR proof became a structural induction, for the
  carrier's hypothesis.
- **Fundamental theorem** (`Validity/Id.v`). `V_id` and `V_idrefl` are
  direct. `V_J` reads the proof's relation as `IdRel` at the carrier's
  relation. At a `refl` whnf, both sides step to the base case. The base
  case's relation moves to the motive instance at `(u, e)` through the
  motive's validity, at the substitution `(u, e) ~ (a, refl)`: the `refl`
  point relates `u` to `a`. At a neutral, `J` is neutral by
  `gne_tm_J`. The right side's typing comes from the congruence
  (`eqtm_J`'s right presupposition), not from its own premises, so no
  context conversion is needed at this level. `VTyS_Jmot` (`ValidS.v`)
  gives the result type's validity.

  In layer M's dispatch, `us_push` exposes `usubst (A⟨↑⟩)` in `J`'s
  motive context after `us_rewrite_all`. One extra pass rewrites
  renamings in the hypotheses (`FundamentalM.v`).
- **Algorithm.** `Id` is `posty`: neutrals at `Id` are compared as
  neutrals. `actnf_id` compares the endpoints at the left carrier.
  `actmne_J` compares every component; the scrutinees are compared as
  neutrals.

  Deviation: `actmnf_refl` accepts **any two `refl`s at an `Id` type**,
  with no premises, where the plan compared carriers and points. Under
  the typings the instances bundle, both points equal the left endpoint,
  by inversion and `Id` injectivity (`id_inj_c`), so the premises would
  be redundant. As at `Unit`, this keeps completeness and decidability
  trivial at this rule. Soundness pays for it with injectivity.

  Soundness, symmetry, transitivity and decidability of `actmne_J` must
  move the other side's motive into this side's context.
  `J_ctx_conv` (an identity substitution) and `J_ctx_eq` (a context
  equality), both in `AlgSound.v`, do that for both binders at once.
- **Consequences.**
  - `id_inj` (`Consequences.v`), with `decl_id_inj` and `declM_id_inj`.
  - `closed_id_canonicity` (`Canonicity.v`): a closed proof of
    `Id^l(A; a; b)` computes to `refl`, and then `a ≅ b`.
  - Preservation covers `J`'s congruence and β at any `refl`.
  - Type uniqueness, type checking (`sy_J` builds the motive context's
    `Id` entry instead of deciding it) and consistency extend.

**Cost.** 59 files, about 2180 lines added and 85 changed, against 1517
in 53 for M10a (two formers, no carrier relation):
- LogRel, about 460;
- the algorithmic families, about 520;
- Typing metatheory, about 520;
- `Validity/Id.v`, 320.

`J`'s two-binder motive accounts for most of the difference. The
algorithmic lemmas each move a motive across contexts (`J_ctx_conv`), and
the typing metatheory needed the regctx lemmas for the shifted `Id`
entry.

Clean build: 217 s wall at `-j2` (168 s before M11a).

## M11b outcome (2026-09-30)

Done in two commits: the code `tmId l s t u : Ty l` at layers D and M
(step 1), then the lift to code and the four recursor branches (step 2).
Every headline theorem stays closed under the global context.

- **Gating, as M8d did for Σ.** `wft_id`, `wf_idrefl`, `wf_J`, `wf_code_id`
  and their congruences (`eqty_id`, `eqtm_idrefl`, `eqtm_J`,
  `eqtm_code_id`) take `i <> lV`, so they hold at C. The computation
  rules `eqtm_J_beta` and `eqty_El_id` keep `compt i`. The inversions
  return `i <> lV`. Downstream, the decision procedures split on
  `layer_eq_dec i lV` instead of `compt_dec i` (`dec_tyId`,
  `sy_code_id`, `sy_refl`, `sy_J`).
- **Static Code** (`StaticCode.v`): `sc_id`, `sc_idrefl`, `sc_code_id`,
  `sc_J` and their `_q` forms. `J`'s cases need layer-generic facts built
  from D-level equations: `J_facts_D` (the motive context's equality and
  the motive's two instances) and `J_ctx_eq'`, the motive contexts'
  equality over *equal* base contexts. `J_ctx_eq` moved here from
  `AlgSound.v`. PresupC gets `pc_id`, `pc_idrefl`, `pc_code_id`, `pc_J`.
- **Recursor** (`Recursor.v`, `RecSpec.v`): `nbr = 25`.
  - `t_Id` is branch 21, a type branch at `l₁`, with `(nu, ng, nl) = (1, 4, 3)`.
  - `t'_Id` is branch 22, `(1, 4, 3)`.
  - `t_refl` is branch 23, `(1, 3, 2)`.
  - `t_J` is branch 24, `(2, 7, 6)`.

  `J`'s scope declares the motive over
  `cvar 2 ,, gv 1 @ ℓ ,, tyId ℓ (gv 1)⟨↑⟩ (gu 0)⟨↑⟩ (var 0) @ ℓ`. The case's
  type is `tyGvar 0 (lsingle2 (gu 1) (tmRefl ℓ (gv 2) (gu 1)))`, and the
  head's type is `tyGvar 3 (lsingle2 (gu 1) (gu 0))`. So the scope has
  global variables at `lshift 1`, and instances at `lsingle2`.
  `subst_lshift1_ty`, `T[lshift 1] = T⟨↑⟩` (`RecWf.v`), turns their images
  back into the rules' `⟨↑⟩` forms. The scope's typing lemmas are
  `wf_gv_up`, `wf_gu_up`, `wf_var0_gv` and `wf_gv_single2`. The
  push-through rewrites were added to `upeel_push` (`usubst_shift*`),
  `gpeel_push` (`gs_shift*`, `gs_single2_ty'`) and `rec_subst_rw`
  (`wkb_subst4/5`).
- **Validity** (`RecS.v`, `RecReduct.v`). `GS_id`, `GS_codeid`, `GS_refl`
  and `GS_J` follow `GS_pair`. `rec_T_id`, `rec_t_codeid`, `rec_t_refl`
  and `rec_t_J` go through `rec_T_br`/`rec_t_br` and the `RT`/`Rt`
  wrappers. `J`'s case relates the motive call over the two motive
  contexts (`J_ctx_eq'` at the right levels for `Tcall`, and at the left
  levels to type the right pieces for the scope substitution).
  `J_facts_D` supplies the case's and the result's type equations.
  RecReduct gains `rr_T_id`, `rr_t_codeid`, `rr_t_refl`, `rr_t_J` and
  the `C_*` cases. The branch-scope tactic `br_tac` (`AlgPrereq.v`) gained
  the `Id` rules.

**Gotchas.**
- The instance of a global declared under a shifted variable is stuck:
  `gsubst` cannot see through `ren (gv n) ↑`. Compute the renaming
  first (`cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]`),
  then rewrite `subst_lshift1_ty`. The same applies to `lsingle2`, a
  definition: `ulsubst`/`glsubst` reduce on it only once it is unfolded.
  `J_cbn` (RecS) does both.
- At layer C, `typeof i ≠ i`. Code built at a generic `i` must use the
  `_g` weakening lemmas (`wk1_ty_g`, `wk1_tm_g`, `var0_wf_g`), not the M1
  forms that take `typeof i = i`. That is how `sy_J` and `wf_Jid_g` are
  written.
- In `rec_t_J`, `all: try solve [J_res]` over the refine's remaining
  goals left the result equations unsolved. One bullet per goal with the
  same tactic worked. The cause was not investigated.

**Cost.** Steps 1 and 2 together: 45 files, about 1690 lines added and
160 changed. RecS accounts for 590 of them, StaticCode for 210 and
RecReduct for 200.

Clean build: 234 s wall at `-j2` (217 s after M11a). `RecAdm`'s
`brΓ_wf`/`brRes_wf` over the 25 branches take about 19 s.

## UIP stated; the no-UIP model checked (2026-09-30)

`Validity/Uip.v` states UIP and checks the no-UIP model's predictions
(Heather `docs/no-uip-model.md` §4.5, §5.1) where the syntax can decide
them. Everything is closed under the global context.

- **`uip_pt l A a b`**, which is `Π(p q : Id(A; a; b)). Id(Id(A; a; b); p; q)`,
  and **`UIP0`**, the model's `UIP₀` at `⌜Nat⌝`. The model uses `⌜Bool⌝`,
  but the development has no sums; any code with a non-identity
  bijection works. `uip_pt_wf` and `UIP0_wf` prove them well-formed
  types at every layer but V, the latter closed in any global context.
- **`uip_unit_wf`**: UIP at `Unit` in the syntax. The model predicts this,
  because `Unit`'s fibre is discrete. The proof is `K` by `J` (motive
  `Id(refl; p')`), then UIP by a second `J` with `K(q)` as the base case.
  `Unit` enters only through η, at the motive's variable endpoint.
- **`closed_id_uip`**: closed proofs of an `Id` type are convertible, by
  `closed_canonicity_whnf` and `refl_refl_eq`, which is inversion and
  `id_inj_c`. It is UIP as a metatheorem for closed terms. The model
  agrees, since closed proofs denote identities. So its counterexample
  (`swap`) is not denoted by any closed term.

The probe gains `no_uip0_nat`, the refutation of `UIP0`'s interpretation.
The model doc's §4.5 checks each `Id` rule of `Declarative.v` against the
groupoid model, and finds no conflict.

`probes/NoUipJ.v` mechanizes the model's `J` in the form of `wf_J`: the
`Id` family over `Γ.A`, `refl`, and `J` as a section of `M[u/y, e/p]`
with its functor laws. β holds on the nose. It is closed under the global
context; its groupoids have sets of objects and morphisms, as in the
set-theoretic model. Stability under substitution is not mechanized.
