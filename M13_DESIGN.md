# M13: well-founded trees (`W`), design

Status: **M13 done, 2026-10-03** (M13a and M13b; outcomes below). Why now: `HEATHER.md`
item 5 lists `W` after `Empty` and `+`, and Heather's paper pass calls it
"the heaviest case" (MX §5). It is the first former whose term relation is
an inductive definition with a Kripke-quantified recursive premise, and the
only β rule whose right-hand side builds a binder found on neither side.

Heather's rules: `H/docs/delam-extensions.md` §9.
- `W^{l,l'}(x : S). T @ l ⊔ l'`, with `T` under the shape's binder.
- `sup^{l,l'}(x : S. T; a; f)`, with the child function
  `f : Π^{l', l ⊔ l'}(y : T[a/x]). W↑`.
- `elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s; t) : M[t/z] @ l''`, a
  dependent motive and a step over the three-entry telescope
  `Γ, a : S, f : fty, ih : ihty`.
- β synthesizes the induction hypothesis
  `IH := λ^{l',l''}(y : T[a/x]). elim_W(…↑; f↑ y)`, and the step is
  instantiated at `a`, `f`, `IH`.
- No η: `W` is positive.
- A code `W^{l,l'}(x : s). t : Ty (l ⊔ l')` and four recursor branches
  `t_W`, `t'_W`, `t_sup`, `t_elimW`.

Every choice above is Heather's. Gating follows M12: the formers at layers
D and M first, then every layer but V with the code (M13b).

## Staging

- **M13a**: `W`, `sup`, `elim_W` and β at layers D and M, gated by
  `compt i`, with no code.
- **M13b**: the code, the lift to C and the four recursor branches.

## Syntax (de Bruijn)

Write `L := l ⊔ l'` and `W := tyW l l' S T`, with `S` in `Γ` and `T` in
`Γ, x : S`.
- `tyW l l' S T`, `T` under one binder.
- `tmSup l l' S T a f`, `T` under one binder.
- `tmElimW l l' l'' S T M s t`, `M` under one binder (the scrutinee `z`),
  `s` under three (`a`, `f`, `ih`, innermost last).

The step telescope, in de Bruijn form:
- `Γ_a = Γ, S`. Here `T` itself is `T[a/x]`: `a` sits where `x` was.
- `fty := Π^{l', L}(y : T). W⟨↑⟩⟨↑⟩`, in `Γ_a`.
- `ihty := Π^{l', l''}(y : T⟨↑⟩). M[↑³, app(var 1; l', L; T⟨↑⟩⟨↑⟩;
  W⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩; var 0)/z]`, in `Γ_a, fty`. The application's
  annotations are `fty` weakened past `f` and `y`, literally.
- The step's type is `M[↑³, sup(S⟨↑³⟩; T⟨rlift ↑³⟩; var 2; var 1)/z]`.

β, at a `sup` of any annotations (as `case` steps at any injection):
`elim_W(S; T; M; s; sup(_; _; a; f)) ⤳ s[a, f, IH]` with
`IH := λ^{l', l''}(T[a/x]). elim_W(S⟨↑⟩; T⟨rlift ↑⟩; M⟨rlift ↑⟩;
s⟨rlift³ ↑⟩; app(f⟨↑⟩; l', L; T[a/x]⟨↑⟩; W⟨↑⟩⟨rlift ↑⟩; var 0))`. The
application's annotations are the child function's type weakened past `y`.

## The relation (design point)

MX §5 sketches `NfEqW`: a `sup` pair is related when the shapes are
related and, in every weakening, the children at related positions are
related by the outer relation at `W`. The recursive occurrence is under the
Kripke quantifier, so the relation is an inductive *family* whose context,
shape and family data change in the recursive premise.

- `WRel G Γ l1 l2 S T domR codR t t'` (with `WNf` mutually), with `G`,
  `Γ`, `S`, `T`, `domR`, `codR` indices. A child premise at `ρ` is at
  `kw_G ρ`, `kw_Δ ρ`, `kty ρ S`, `ktyl ρ T`, and the data composed with
  `ρ` (`fun ρ' => domR (kw_comp ρ ρ')`, as Weakening builds Π's).
- No identity weakening is needed: shapes are related in every weakening
  (`∀ ρ, domR ρ (ktm ρ a) (ktm ρ a')`), as `SigRel` relates first
  projections. The child premise quantifies over every proof `ha` of the
  shapes' relation at `ρ`, so the definition needs no weakening lemma for
  `domR`.
- Child applications are related for every choice of equivalent
  annotations, as in `PiRel`.
- The weakened data are not definitionally the composed data
  (`kw_comp` is associative only propositionally), so the relation's
  weakening, irrelevance and symmetry go through one transport lemma: `WRel`
  respects generically equal `S`, `T` and pointwise equivalent `domR`,
  `codR` (`codR` for any two proofs of the shapes' relation).
- The type relation `LRw` has `Σ`'s shape (`PolyFacts` at `tyW`, `domR`
  and `codR` in every weakening).
- The children's functions reduce to related whnfs in every weakening:
  `∀ ρ, WhRel … (Π^{l', L}(y : (ktyl ρ T)[ktm ρ a]). W↑) (ktm ρ f)
  (ktm ρ f')`, where `WhRel` is the first clauses of `PiRel` (both sides
  reduce, at the left type, to whnfs related generically). Without it a
  child function is related only through its applications, which does not
  say it has a whnf, and `elim_W`'s step takes `f` as an argument of type
  `fty`: its validity needs `f` related at `fty`, which is `PiRel`.
  Found when writing `elim_W`'s validity; added 2026-10-01. Kripke (not at
  the identity world) so that weakening composes it and symmetry,
  transitivity and level invariance convert its type at each world with
  the codomain's escape, as they do the annotations.
- The relation's lemmas: `WRel_dir`/`WRel_releq` (Escape), `WRel_flip`
  (Symmetry), `WRel_trans` (Transitivity, with `WhRel_trans`), `WNf_kw`/
  `WRel_kw` (Weakening), `WRel_leq` (LevelInv) and `WRel_perm` (UPermLR,
  over worlds that correspond along the permutation, `kcorr`; the backward
  direction is the forward one along `πi`).

## M13a outcome (2026-10-01)

Done at layers D and M. Every headline theorem stays closed under the
global context (`Print Assumptions` of `wf_tm_dec`, `V_elimW_sup`,
`closed_W_canonicity` and `T_actmne_elimW` lists nothing), and
`closed_W_canonicity` is new.

- **Syntax and rules** as above, gated by `compt i`: `wft_W`, `wf_sup`,
  `wf_elimW`, their congruences, and β at a `sup` that carries the
  `elim_W`'s own annotations (`eqtm_elimW_sup`). `wf_elimW` takes the
  telescope's types (`wfty`, `wihty`) as premises, so inversion returns
  them. β at other annotations follows from injectivity of `W`
  (`RS_elimW_sup`). Presupposition gains the telescope lemmas
  (`W_fty_wf`, `W_ih_wf`, `W_ih_eq`, `W_step_eq`) and the synthesized
  induction hypothesis's (`W_IH_wf`, `W_IH_eq`): β's right-hand side is
  well formed and congruent.
- **Relation**: `LRw` with `WRel`/`WNf`, as designed above, plus the
  `WhRel` premise on child functions.
- **Validity** (`Validity/W.v`, `Validity/WElim.v`): `V_W`, `V_sup`,
  `V_elimW` and `V_elimW_sup`. `elim_W` is related by induction on
  `WRel` (`elimW_core`) at every global weakening and related
  substitution, with motive `elimW_mrel`. At a `sup` both sides step to
  the step at the shape, the child function and `wIH`, a λ whose
  applications step to `elim_W` at the children, related by the
  induction hypothesis (`elimW_step`). The global-substitution layer
  (`RulesS`) and `FundamentalM` extend; the latter runs its universe
  substitution pass twice when `W` is in the goal, since `B[a]` and
  `W⟨↑⟩` inside `fty` expose a push only after the first pass.
- **Algorithm**:
  - `W` is `posty`. `sup`s are compared by shape and by child function,
    both at the left side's types (`actmnf_sup`); `elim_W` is a neutral
    whose step is compared in the left side's telescope at the left side's
    step type (`actmne_elimW`).
  - `AlgSound.v`: `W_inj_c`, `sup_parts` (a typed `sup`'s parts at its
    type's annotations), `fty_conv` (child function types at equal shapes
    are equal), `W_ctx_conv` and `elimW_step_left` (the right step moved
    into the left telescope along the identity).
  - `AlgPER.v`: `W_tele_eq` (two telescopes with equal parts are equal
    contexts both ways, with equal step types). Symmetry moves the swapped
    step into the right telescope; transitivity moves the second
    comparison's step from the middle telescope to the left.
  - Conversion, lifting, decidability and the `AlgEq` laws (`geq_ty_W`,
    `geq_tm_sup`, `gne_tm_elimW`) extend.
- **Consequences**:
  - `closed_W_canonicity`: a closed term of `W` computes to a `sup` whose
    shape and child function are closed terms of the shape type and of the
    child function type at that shape.
  - Canonicity's head table lists `sup` at `W` (head 17).
  - Preservation (`RS_elimW`, `RS_elimW_sup`), type uniqueness,
    consistency (`neutral_univ`) and type checking (`dec_tyW`, `sy_sup`,
    `sy_elimW`; `elim_W`'s step type is built from the decided shape,
    positions and motive) extend.

**Cost.** 58 files, about 5000 lines added: `Validity/W.v` and
`Validity/WElim.v` are 1220 lines, the relation's files about 1260, the
typing presupposition about 700 and the algorithmic families about 870.
The clean build takes 443 s (from 426 s after M12c; Hedberg's files,
added in between, are part of the difference).

## M13b outcome (2026-10-03)

Done in two commits, on M12c's pattern. Every headline theorem stays
closed under the global context (`Print Assumptions` of `wf_tm_dec`,
`paper_sound`, `rec_red_typed`, `subject_reduction_tm`, `consistency`,
`V_elimW_sup`, `closed_W_canonicity` and `T_actmne_elimW` lists nothing).

- **Step 1, the code at D and M**: `tmW l l' s t : U (l ⊔ l')`, with `t`
  under the shape's binder at `El s`, as `Σ`'s code. It decodes to `W`
  (`eqty_El_W`). Validity, the algorithm, preservation, canonicity and the
  type checker extend as for the other codes.
- **Step 2, the lift to C**: `W`'s formation and congruence, `sup`,
  `elim_W` and the code take `i <> lV`; β and `El` stay at `compt i`, as
  M11b and M12c did. The algorithm and preservation reach the lifted rules
  through `compt_notV`. The type checker decides `W`, `sup` and `elim_W`
  at every layer but V: `sy_sup` and `sy_elimW` build the types they check
  against at `typeof i` (the shape's instance of the positions, the step
  type), and `elim_W`'s telescope at `i` with `StaticCode`'s generic
  `WGen` lemmas (`W_fty_wf_i`, `W_ih_wf_i`), which need only `i <> lV`.
- **The four branches** are 39–42 (`nbr = 43`): `t_W`, `t'_W`, `t_sup`,
  `t_elimW`, with (levels, globals, locals) `(2,3,2)`, `(2,3,2)`,
  `(2,5,4)`, `(3,6,5)`. `t_W` and `t'_W` are `Σ`'s. `t_sup`'s child
  function is declared at `Π(y : U_T^{u_a/x}). (W U_S U_T)↑`, its call at
  that type. `t_elimW`'s step is declared over `g, x : U_S, f : wfty,
  h : wihty` at `wstepty`, the telescope M13a derived from the semantics
  (it agrees with Heather's `rec.rs`).
- **Static code and presupposition**: `sc_W`, `sc_sup`, `sc_elimW`,
  `sc_code_W` (with `_q` forms at given right-hand annotations).
  `W_sup_feq` (the children's types along equal components) and `W_facts`
  (an `elim_W` congruence's scrutinee types, motive contexts, step
  contexts and step types, in one lemma) carry the side conditions both
  validity and the reducts need.
- **Scope automation** (`RecWf`). The W scopes' entries mention the step
  telescope, whose instances only match a typing rule after computation,
  and the eager `br_ctx`/`wfd` style rederived each prefix at every leaf.
  So the W scopes get memoised tactics: `wctx` proves a context once and
  keeps it as a hypothesis, `wbind` types a binder's domain and its
  extended context once for the body, `wty`/`wtop` dispatch by head, and
  the `_eq` rules (`wf_var_eq`, `wf_app_eq`, `wf_sup_eq`, `wf_elimW'`) take
  the computed type up to an equation. `AlgPrereq`'s `br_tac` hands any
  goal mentioning `tyW`, `tmW` or `tmElimW` to `wnorm; wtop`, after
  unfolding `gv`/`gu` (otherwise a weakened `gv` stays stuck under
  `ren`).
- **Keeping the telescope folded.** `wfty`, `wihty` and `wstepty` are
  notations, so a plain `cbn` of a substitution through them unfolds their
  weakenings into `subst_ty` forms that no longer match the typing
  rule's, and mutual-fixpoint `cbn` leaves `fix gsubst_ty` residues. The
  fix is to push global and universe substitutions through them whole by
  rewriting (`gs_wfty`, `gs_wihty`, `gs_wstepty`, `us_*`, and `uc_ext`/
  `gc_ext` for context extensions), then `cbn` with renamings left alone.
  `RecS`'s `sr_ctx_W` and `RecReduct`'s `rr_ctx_W` are `sr_ctx`/`rr_ctx`
  with that order. `eqc_ext_inv` inverts a context-extension equality
  without `repeat split` (which split `lequiv` too).
- `RecS` has `rec_T_W`, `rec_t_codeW` (the `Σ` lemmas, copied),
  `rec_t_sup` (on `rec_t_pair`'s pattern, the right child function put
  at the left levels through `W_sup_feq`) and `rec_t_elimW` (on
  `rec_t_case`'s, with `W_facts` at both sides' levels); `RecReduct` has
  `rr_T_W`, `rr_t_codeW`, `rr_t_sup`, `rr_t_elimW` and the `C_*` entries.

**Cost.** Step 1: 31 files, about 510 lines. Step 2: 27 files, about
1530 lines added and 140 changed, of which `RecS` is 620, `StaticCode`
230, `RecReduct` 190 and `RecWf` 130.
