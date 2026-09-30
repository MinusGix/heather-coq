# M12: the empty type and binary sums (`Empty`, `+`), design

Status: **M12a and M12b done, 2026-09-30** (outcomes below). Why now: `HEATHER.md`
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

## M12b outcome (2026-09-30)

Done at layers D and M. Every headline theorem stays closed under the
global context, and `closed_sum_canonicity` is new.

- **Syntax**: `tySum l l' A B`, `tmInl l l' A B a`, `tmInr l l' A B b` and
  `tmCase l l' l'' A B M c1 c2 t`. The motive binds the scrutinee, and
  each branch binds its payload at the branch type
  `M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))]`, the motive at the
  injection of the bound variable. `case` reduces its scrutinee and steps
  at an injection of any annotations, and it is `whne` on a `whne`
  scrutinee.
- **Rules**, gated by `compt i`: `wft_sum`, `eqty_sum`, `wf_inl`,
  `wf_inr`, `wf_case`, their congruences, and both β rules at an injection
  that carries the `case`'s own annotations (`eqtm_case_inl`,
  `eqtm_case_inr`). β at other annotations follows from injectivity of
  `+` (`RS_case_inl`).
- **A second rewrite pass.** The branch types put the shifted summands
  inside an injection, so pushing a renaming or substitution through them
  exposes a shift only after the first pass. Every such normalizer runs
  twice: declarative weakening, global weakening, substitution and
  universe substitution, and the algorithm's three. Running the second
  pass only when an injection is in the goal was slower than running it
  always, because the search through the goal costs more.
- **Relation** (`LRsum`, `SumRel`, `SumNf`): a term reduces either to an
  injection whose payload is related at its summand, or to a neutral. The
  constructor carries the summands' derivations and their PER facts, as
  `LRid` does for its carrier. Both summands live in `Γ`, so there is no
  Kripke quantification. An injection's annotations need only be
  equivalent to the type's (`lequiv` and generic `≈`).
- **Validity** (`Validity/Sum.v`):
  - `V_sum`, `V_inl`, `V_inr`, `V_case`, `V_case_inl` and `V_case_inr`.
  - At an injection, `case` steps to its branch. The branch's type, the
    motive at the injection, is converted to the motive at the scrutinee
    through the motive's validity at the two related terms.
  - At a neutral, `case` is neutral (`gne_tm_case`).
- **Algorithm**:
  - `+` is `posty`. Injections are compared by payload (`actmnf_inl`,
    `actmnf_inr`), and `case` as a neutral whose branches are compared at
    the left side's branch types (`actmne_case`).
  - `case_right_left` (`AlgSound.v`) moves the right side's premises
    (motive, branches, scrutinee) to the left side's contexts. Soundness,
    conversion, symmetry, transitivity and decidability all use it;
    transitivity uses it three times, since the second comparison is at
    the middle side's contexts.
  - Soundness at the injections needs injectivity of `+` (`sum_inj`, from
    the relation, at D and M).
- **Consequences**:
  - `closed_sum_canonicity`, the disjunction property: a closed term of
    `A + B` computes to an injection whose payload is a closed term of its
    summand.
  - Canonicity's head table lists the injections at `+`.
  - Preservation (`RS_case`, `RS_case_inl`, `RS_case_inr`), type
    uniqueness, type checking (`dec_tySum`, `sy_inl`, `sy_inr`, `sy_case`)
    and `neutral_univ` extend.

**Cost.** 54 files, about 2470 lines added: `Validity/Sum.v` is 430 lines,
the relation's files about 510 and the algorithmic families about 560.
The clean build takes 326 s (from about 250 s). Most of the growth is in
the Syntax metatheory and the algorithm, whose case analyses over terms
gained three constructors (`AlgDec` alone is about 10 s slower), plus
about 6 s for the second normalizer pass in `AlgStruct`.
