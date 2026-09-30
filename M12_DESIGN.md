# M12: the empty type and binary sums (`Empty`, `+`), design

Status: **M12a done, 2026-09-30** (outcome below). Why now: `HEATHER.md`
item 5 lists the positive formers after `Id`. `Empty` and `+` are the
smallest: with them the development has `⌜Bool⌝ = Unit + Unit`, so the
no-UIP model's `UIP₀` can be stated as Heather's `docs/no-uip-model.md`
writes it. Hedberg's theorem needs `¬` (`Empty`) and decidable equality
(`+`), so the model's positive prediction becomes checkable in the syntax
as well.

Heather's rules: `H/docs/delam-extensions.md` §7 (`Empty`) and §8 (`+`).
- `Empty^l @ l`, level-indexed. It has no introduction, no β and no η.
  `Empty`-η (proof irrelevance at `Empty`) is an open Heather issue
  (`issues/empty-eta-conversion.md`), not a rule, and it has no customer.
- `elim_Empty^{l,l'}(x. M; t) : M[t/x] @ l`, for `t : Empty^{l'}`. The
  motive binds the scrutinee, and its level `l` is independent of the
  scrutinee's `l'`.
- `A +^{l,l'} B @ l ⊔ l'`, non-dependent: both summands live in `Γ`.
- `inl^{l,l'}(A; B; a)` and `inr^{l,l'}(A; B; b)`, each carrying both
  summands.
- `case^{l,l',l''}(A; B; z. M; x. c_l; y. c_r; t) : M[t/z]`, with a
  dependent motive and both β rules.
- `+` has no η: it is a positive type.
- Codes `Empty^l : Ty l` and `a +^{l,l'} b : Ty (l ⊔ l')`.
- Eight recursor branches: `t_Empty`, `t'_Empty`, `t_elimE`, `t_+`,
  `t'_+`, `t_inl`, `t_inr` and `t_case`.

Every choice above is Heather's, so there is no fork to settle. Gating
follows M11: the formers are at every layer but V, and β at D and M.

## Staging

- **M12a**: `Empty` and `elim_Empty` at layers D and M, gated by
  `compt i`, with no code.
- **M12b**: `+`, `inl`, `inr`, `case` and β at D and M, with no code.
- **M12c**: the two codes, the lift to the code layer and the eight
  recursor branches, as M11b did for `Id`.

## M12a outcome (2026-09-30)

Done at layers D and M. Every headline theorem stays closed under the
global context.

- **Syntax**: `tyEmpty l` and `elimEmpty l l' M t`, where `M` is under
  one binder, the scrutinee. The motive's level comes first, as in
  Heather's `elim_Empty^{l,l'}`. The eliminator reduces its scrutinee
  only, and it is `whne` on a `whne` scrutinee.
- **Rules**, gated by `compt i`: `wft_empty`, `eqty_empty`,
  `wf_elimEmpty` and `eqtm_elimEmpty`. The motive premise is
  `[Γ ,, Empty^{l'} ⊢ M @ l]`, as `natrec`'s is over `Nat`. Weakening
  and substitution need only the hints `wf_ctx_empty` and
  `wft_empty_typeof`. Functionality has an `elimEmpty` case built on
  `natrec`'s. Static Code has a D-only section again (`SCD`), for
  `sc_empty` and `sc_elimEmpty`.
- **Relation** (`LRempty`, `EmptyRel`), as logrel-coq's `Empty`: terms
  reduce to neutrals, and the two neutrals are related generically.
  Unlike `sEmpty`'s relation, which relates each neutral to itself, this
  one compares them, since `Empty` has no η. Adding the constructor
  meant one new clause in each of the 31 positional case analyses of the
  relation. Those were inserted by script, next to `LRsempty`'s clause,
  which has the same shape.
- **Validity** (`Validity/Empty.v`):
  - `V_empty`.
  - `V_elimEmpty`. The scrutinees reduce to related neutrals, so the
    eliminator is neutral (`gne_tm_elimEmpty`).
  - The motive's instances are related through its validity at the
    lifted substitution (`VTy_empty_at`). The instance at the neutral and
    the instance at the scrutinee are related by `EmptyRel_to_ne`, a term
    and its neutral reduct.
- **Algorithm**:
  - `Empty` is `posty`, so its neutrals are compared as neutrals, with no
    irrelevance arm.
  - `actnf_empty`.
  - `actmne_elimEmpty` compares the motives at the left scrutinee's
    context `Γ ,, Empty^{l2}` and the scrutinees as neutrals.
  - Symmetry, transitivity, conversion and decidability move the other
    side's motive from `Γ ,, Empty^{l4}` to `Γ ,, Empty^{l2}` with
    `stab_ty`.
- **Consequences**:
  - `closed_empty_empty`: no closed term of `Empty` at D and M. It is
    consistency at `Empty`, proved as `closed_sempty_empty` was.
  - Preservation (`RS_elimEmpty`), type uniqueness, type checking
    (`dec_tyEmpty`, `sy_elimEmpty`) and `neutral_univ` extend.

**Cost.** 51 files, about 860 lines added and 60 changed. `Validity/Empty.v`
is 130 lines, and the algorithmic families take about 200 lines. It is
cheaper than M10a (1450 lines for two formers) or M11a (2180). A relevant
type with no canonical form reuses the neutral machinery.
