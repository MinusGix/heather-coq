# M11: the identity type (`Id`, `refl`, `J`), design

Status: **M11a done, 2026-09-30** (outcome below); M11b next. Why now: the no-UIP model
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
