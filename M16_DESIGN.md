# M16: propositional truncation (`Squash`), design

Status: **M16a done** (2026-10-10; outcome at the end), M16b (the code
and the recursor branches) next. Why now: `HEATHER.md` item 5
lists `Squash` as the last former of Heather's kernel without a check here,
and its relation was settled by a probe (`probes/SquashProbe.v`,
heather-coq#8). Heather's `issues/metatheory-ch07-squash.md` owns the full
ch. 07 pass; this milestone is that pass, machine-checked.

Heather's rules: `H/issues/sprop-squash.md` (the working eliminator, landed
2026-08-25), `H/crates/kernel/src/{typing,reduce,conv,rec}.rs`, paper sketch
`H/docs/metatheory-ch07-extensions.md` §27.
- `∥A∥^l @ l`, for `A @ l`. Level-indexed like `Unit`, `Empty`, `sEmpty`.
- `squash^l(A; a) : ∥A∥^l`, for `a : A`. Annotated, synthesizes.
- `ind_∥∥^{l,l'}(A; z. B; x. b; q) : ∥B[q/z]∥^{l'} @ l'`, for
  `q : ∥A∥^l`, the motive `B @ l'` over `z : ∥A∥^l`, and the step
  `b : ∥B[squash x / z]∥^{l'}` over `x : A`. The result is again a squash:
  the "squash-headed" restriction, so the kernel needs no classifier of
  propositions. The source level comes first, as in Heather's
  `ElimSquash { src_level, dst_level, .. }`.
- β: `ind_∥∥(squash(a); z.B; x.b) ⇝ b[a/x]`, at a `squash` of any
  annotations (`reduce.rs`).
- Definitional proof irrelevance: any two terms of `∥A∥^l` are equal
  (`conv.rs`, the `TyView::Squash` arm). Conversion first brings both sides
  to weak-head normal form, then ignores them: MX §27's
  "normalizing-total" rule.
- The neutral eliminator compares the levels, the carriers and the motives,
  and neither the scrutinees nor the steps (`conv.rs`, `ElimSquash`).
- A code `∥s∥ : Ty l` and four recursor branches (`ty_squash`,
  `tm_squash`, `tm_squash_in`, `tm_elim_squash`, `rec.rs`).
- No bridges into `sEq` or `sEmpty` (Heather's scope point (a)).

Every choice above is Heather's. Gating follows M12–M15: the formers at
layers D and M first, then every layer but V with the code.

## Staging

- **M16a**: `Squash`, `squash` and `ind_∥∥` at layers D and M, gated by
  `compt i`, with β and proof irrelevance, and every consequence. No code.
- **M16b**: the code, the lift to layer C and the four recursor branches
  (after M15b's genericity step 0, `br_calls` derived from the scopes).

## Syntax (M16a)

- `tySq l A`: `∥A∥^l`, no binder.
- `tmSq l A a`: `squash^l(A; a)`.
- `tmElimSq l l' A M c t`: `ind_∥∥^{l,l'}(A; z. M; x. c; t)`, with `M`
  under one binder (the scrutinee) and `c` under one (the payload).

They are appended to `ty` and `tm` after `Wf`'s. The step's type is the
motive at the squash of the bound payload, written as `case`'s branch
types are (M12b):
`tySq l' M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))]` in `Γ, x : A`.

Reduction: `red_elimSq_sq` (β at any annotations) and `red_elimSq` (the
scrutinee reduces). `tmSq` is `whnf`, `tySq` is `whnf_ty`, and `tmElimSq`
is `whne` on a `whne` scrutinee.

## Rules (M16a, gated by `compt i`)

- `wft_sq`, `eqty_sq`: formation and its congruence.
- `wf_sq`, `eqtm_sq`: `squash` and its congruence.
- `wf_elimSq`, `eqtm_elimSq`: the eliminator and its congruence.
- `eqtm_elimSq_sq`: β, at a `squash` carrying the eliminator's own
  annotations. β at other annotations follows from injectivity of `∥·∥`
  (`RS_elimSq_sq`), as `case`'s does from `+`'s.
- `eqtm_sq_irr`: proof irrelevance, as `eqtm_seq_irr` and
  `eqtm_empty_irr`.

Irrelevance subsumes both term congruences. They are rules anyway, as
`srefl`'s is (M10a): the substitution and functionality lemmas then need
no conversion of the result type.

## The relation (design point: the probe's clause)

`probes/SquashProbe.v` checked the clause against the development's LR with
the former abstract. M16a adds it as it stands:

- `SqNf G Γ l A RA w`: a whnf at `∥A∥` is good **alone** when it is
  `squash^k(C; a)` with `k ≡ l`, `A ≈ C` and `RA a a` (the payload related
  to itself), or a neutral `ν ~ ν`.
- `SqU G Γ l A RA t`: `t` reduces to a good whnf at `∥A∥^l`.
- `SqRel G Γ l A RA t t' := SqU … t /\ SqU … t'`: a product of two unary
  predicates. Nothing about `t` is compared with anything about `t'`.
- `LRsq`: the type clause keeps the carrier's derivation and its relation
  `RA` at `Γ` (not in every weakening, as `LRsum`'s summands), the PER facts
  of `RA`, and `R ⇔ SqRel`.

Why each part:
- The payload's self-relation is what the eliminator needs:
  `ind(squash a; z.B; x.b) ⇝ b[a/x]` instantiates `b`'s validity at `a`,
  which needs `a` in `A`'s relation. Typing alone does not give it. This
  is the probe's one refinement of MX §27, which asks for no relation on
  payloads.
- Neutrals are self-related, as at `Empty` since its η (M12_DESIGN.md, last
  section): the eliminator is neutral on a neutral scrutinee, and its
  neutral law needs `ν ~ ν`.
- Normalization is the existing shape: `UnitRel`, `SEqRel` and `EmptyRel`
  already keep both sides' whnfs.

The generic equivalence gains three laws:
- `geq_ty_sq`: the congruence of `∥·∥`;
- `geq_tm_sq_irr`: proof irrelevance, where escape for terms comes from;
- `gne_tm_elimSq`: `ind_∥∥` is neutral on neutral scrutinees, each
  related to itself (`Empty`-η's shape), given equal carriers and motives
  and generically equal steps.

## Validity (M16a)

- `V_sq`, `V_sq_intro`, `V_sq_irr` and the congruences.
- `V_elimSq`: each scrutinee is analysed alone (`SqU`'s case split, the
  probe's `SqU_cases`).
  - At a `squash a` with `RA a a`, `ind` steps to `b[a/x]`, which the
    step's validity at the payload puts in `SqU` at `∥B[squash a]∥`; the
    motive's validity moves it to `∥B[q]∥`.
  - At a self-related neutral, `ind` is neutral (`gne_tm_elimSq`).
  - The result relation is again a product, so the two sides' results are
    never compared either.
- `V_elimSq_sq`: β.

## Algorithm (M16a)

- `∥·∥` is not `posty`: `actmnf_sq_irr` relates any two whnfs at a squash
  type, as `actmnf_empty_irr`. The comparison reaches it after both terms
  are in whnf, which is Heather's "normalizing-total" conversion.
- `actnf_sq` compares the levels and the carriers.
- `actmne_elimSq` compares both levels, the carriers and the motives
  (at the left carrier's context), and asks only that both scrutinees be
  neutral. The steps are not compared. This is Heather's `conv.rs` arm.

## Consequences to extend

Injectivity (`sq_inj`, from the relation), canonicity's head table
(`squash` at `∥·∥`), closed canonicity at `∥·∥` (a closed term computes to a
`squash`), preservation (`RS_elimSq`, `RS_elimSq_sq`), type uniqueness,
type checking and `neutral_univ`.

## M16a outcome (2026-10-10)

Done at layers D and M, as designed; the probe's clause went in unchanged.
Every headline theorem stays closed under the global context: `Print
Assumptions` of `consistency`, `decl_eqtm_dec_any`, `closed_canonicity`,
`fundamentalS`, `fundamentalM`, `type_uniq` and `red_sound_tm` lists
nothing.

- **Syntax, typing, reduction** as designed. The step's type needs the
  same presupposition work as `case`'s branches: `sq_branch_r` moves a
  step to the other side's carrier and motive (by `case_branch_eq`), and
  `pre_elimSq_r` types the right eliminator at the left's type.
- **The relation** is `LRsq` with `SqNf`, `SqU` and `SqRel`
  (`LogRel/Def.v`). It keeps the carrier's derivation at `Γ` only and the
  PER laws of its relation; symmetry needs those laws for the flipped
  carrier's relation. `SqRel` itself is symmetric and transitive as a
  product of unary predicates (`SqRel_sym`, `SqRel_trans`), and
  `SqRel_conv` moves it along a carrier conversion, with `LR_irrel`
  relating the two carriers' relations. Escape for terms is
  `geq_tm_sq_irr`. Level inversion (`ty_leq_sq_inv`) and the universe
  permutation (`SqRel_perm`) extend as `+`'s.
- **Validity** (`Validity/Squash.v`) works with one unary predicate,
  `SqG := SqU` at the carrier's canonical relation: `LRtm_sq_inv` and
  `LRtm_sq_of` translate between it and the term relation, and
  `SqG_conv`, `SqG_red` and `SqG_ne` transport it. `V_elimSq` is proved
  for each side alone (a local `Side` assertion): β through
  `red_elimSq_sq` and `eqtm_sq_irr`, and the neutral case through
  `gne_tm_elimSq` with the scrutinee related to itself on each side.
  `V_sq_irr` takes an unused `lwf` first argument, as `V_empty_irr`, so
  the `RulesS` dispatch treats them alike. `RulesS` gains `VS_sq`,
  `VS_sq_single`, `VS_sq_intro`, `VS_sq_single_sq`, `VS_sq_irr`,
  `VS_elimSq` and `VS_elimSq_sq`.
- **The fundamental theorem at M**: `FundamentalM`'s second
  `us_rewrite_all` pass now also triggers on a `tySq` goal. Otherwise
  `usubst_ty M[lsingle t] φ` stays unpushed under the squash around the
  eliminator's motive (the same gotcha as `Wf`'s in M15a).
- **Algorithm** as designed: `actnf_sq`, `actmnf_sq_irr` and
  `actmne_elimSq` through soundness (`S_*`: the right step is moved to the
  left's step type by `sq_branch_r` with the roles swapped, then
  irrelevance relates the steps and the scrutinees), conversion (`C_*`),
  symmetry and transitivity (`Y_*`, `T_*`; `ainv_sq`, `ainv_elimSq`), the
  `AlgEq` laws and decidability (`Dc_*`). `ind_∥∥` joins the neutral-head
  tables (`ne_head`, `is_whne`, `tm_con`).
- **Consequences**: injectivity (`sq_inj`, its D/M instances
  `decl_sq_inj`, `declM_sq_inj`, and `sq_inj_c`), canonicity's head table
  (head 19: a closed term at `∥A∥` computes to a `squash`), preservation
  (`RS_elimSq`, and `RS_elimSq_sq` at any annotations by `sq_inj_c` and
  irrelevance), `neutral_univ`, type uniqueness (`inva_sq`, `inva_elimSq`)
  and type checking (`dec_tySq`, `sy_sq`, `sy_elimSq`, deciding `compt i`
  first with `compt_dec`).
- **Gotchas**: `sq_branch_r` takes `Hi` but not `Hv` outside its section
  (its proof never uses `Hv`), unlike most of its neighbours. `wf_conv`'s
  equation runs from the target type to the source type. In `AlgPER`'s
  `T_actmne_elimSq`, stating the context move once as a local lemma
  (`Back`) avoids three copies of the same `stab_ty` argument.

**Cost.** 56 files, about 1580 lines added (the probe estimated 55 files
and 1500 to 2000 lines), 300 of them in the new `Validity/Squash.v` and
120 in presupposition. A clean `make -j2` took 1297 s wall on
the 2026-10-10 cloud machine of this round (critical path 1071 s, total CPU
1678 s), where the M15b tree measured 1234 s (critical path 1023 s, total
CPU 1585 s) the same day: about 5% more on each. This machine is slower
than the one M15b was first measured on (887 s).
