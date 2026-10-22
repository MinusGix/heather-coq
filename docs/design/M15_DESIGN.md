# M15: finitary well-founded trees (`Wf`), design

Status: **M15 done**: M15a (2026-10-06) and M15b (2026-10-10, the code,
the lift to C and the four recursor branches); outcomes at the end. Why now: `HEATHER.md` item 5
lists `Wf` after `Vec` and `Fin`, which M14 provided, and Heather's
branching inductives lower to it (`H/docs/wf-former-design.md`,
`H/docs/branching-inductives-choice.md`), so an unsoundness here would reach
library code. It also settles the four `Wf` slots of
`H/issues/uncovered-formers-recursor-rules.md` (the code-recursor bindings
nothing outside the kernel attests), by deriving them from the typing rules
below rather than from `rec.rs`.

Heather's rules: `H/docs/wf-former-design.md` §§1.3–5,
`H/crates/kernel/src/{typing,reduce,term}.rs` (`Type::Wf`, `Term::Supf`,
`Term::ElimWf`, `term::nth`, `term::wf_step_telescope`), paper pass
`H/docs/metatheory-ch07-extensions.md` §§11–17 (MX below).
- `Wf^l(x : S). n @ l`, for `S @ l` and `n : Nat @ 0` in `Γ, x : S`. The
  arity is a term, so it contributes no level: `Wf` lives at `l` alone.
- `sup_f^l(x : S. n; a; cs) : Wf`, for `a : S @ l` and
  `cs : Vec^l(Wf; n[a/x]) @ l`: the children are a tuple, not a function.
- `elim_Wf^{l,l'}(x : S. n; z. M; a cs ih. s; t) : M[t/z] @ l'`, with the
  step over `Γ, a : S @ l, cs : Vec^l(Wf; n[a/x]) @ l,
  ih : Π^{0,l'}(i : Fin n[a/x]). M[nth^l(Wf; n[a/x]; cs; i)/z]`.
- β synthesizes the induction hypothesis as a λ over a `Fin` index:
  `elim_Wf(…; sup_f(_; a; cs)) ⤳ s[a, cs, λ^{0,l'}(i : Fin n[a/x]).
  elim_Wf(…↑; nth^l(Wf↑; n[a/x]↑; cs↑; i))]`.
- No η: `Wf` is positive, as `W`.
- `nth` is not a former: it is a fixed `elim_Nat` schema
  (`term::nth`), materialized by the typing rule and by β.
- A code `Wf^l(x : s). n : Ty l` and four recursor branches `t_Wf`,
  `t'_Wf`, `t_supf`, `t_elimWf`.

Every choice above is Heather's. Gating follows M13 and M14: the formers at
layers D and M first (gated by `compt i`), then every layer but V with the
code.

## Staging

- **M15a**: `Wf`, `sup_f`, `elim_Wf` and β at layers D and M, through the
  logical relation, validity, the algorithm, decidability and the
  consequences. No code.
- **M15b**: the code, the lift to C and the four recursor branches 47–50
  (`nbr = 51`). Their scopes are derived below already, because that is
  the part `uncovered-formers-recursor-rules` asks for.
  Step 0 is the narrow genericity pass decided in `HEATHER.md`
  (direction 1): calls derived from `brDecls`, a generic `GS_br`, a
  per-call lemma and an `RT_`/`Rt_` tactic, with its abort criterion.

## Syntax (de Bruijn)

Write `Wf := tyWf l A N`, with `A` in `Γ` and `N` in `Γ, x : A`.
- `tyWf l A N`, `N` under one binder.
- `tmSupf l A N a cs`, `N` under one binder.
- `tmElimWf l l'' A N M c t`, `N` and `M` under one binder (`M` binds the
  scrutinee `z`), `c` under three (`a`, `cs`, `ih`, innermost last).

`nth` is a Coq definition, `tmNth l T k cs i`, transcribing `term::nth`
literally (all four arguments in `Γ`):

```
tmNth l T k cs i :=
  app (app (natrec l Mot base step k) l l (Vec^l(T; k)) (Π^{0,l}(Fin k↑). T↑↑) cs)
      0 l (Fin k) T↑ i
Mot  (Γ, k̂)          := Π^{l,l}(Vec^l(T↑; k̂)). Π^{0,l}(Fin k̂↑). T↑↑↑
base (Γ)             := λ^{l,l}(Vec^l(T; 0)). λ^{0,l}(Fin 0). elim_Empty^{l,0}(T↑↑↑; var 0)
step (Γ, k̂, r)       := λ^{l,l}(Vec^l(T↑↑; S k̂)). λ^{0,l}(Fin (S k̂↑)).
                          case^{0,0,l}(Unit^0; Fin k̂↑↑; T↑⁵;
                                       fst(cs); r (snd cs) j; i)
```

with `fst`/`snd` annotated at `Σ^{l,l}(T↑⁵). Vec^l(T↑⁶; k̂↑)` and the
recursive call's applications annotated as the outer ones (this is
`term::nth`, binder by binder). `nth` types at layers D and M only: the
`case` scrutinee `i : Fin (S k̂)` meets `Unit + Fin k̂` through `Fin`'s
reduction. At C it types through `wf_conv`, whose equation is at
`typeof C`, which computes (relevant to M15b, not a departure).

The step telescope, as notations (M13b's lesson: keep it foldable):
- `Γ_a = Γ, A`. Here `N` itself is `N[a/x]`: `a` sits where `x` was.
- `wfcsty := Vec^l(Wf↑; N)`, in `Γ_a`.
- `wfihty := Π^{0,l''}(i : Fin N↑). M⟨⇑↑⟩³[nth^l(Wf↑³; N↑↑; var 1; var 0)/z]`,
  in `Γ_a, wfcsty`, declared at `lmax 0 l''`.
- The step's type is `M⟨⇑↑⟩³[sup_f^l(A↑³; N⟨⇑↑⟩³; var 2; var 1)/z]`.

β, at a `sup_f` of any annotations (as `elim_W`):
`elim_Wf(A; N; M; c; sup_f(_; _; a; cs)) ⤳ c[a, cs, wfIH]` with
`wfIH := λ^{0,l''}(Fin N[a/x]). elim_Wf(A↑; N⟨⇑↑⟩; M⟨⇑↑⟩; c⟨⇑³↑⟩;
nth^l(Wf↑; N[a/x]↑; cs↑; var 0))`.

## Rules (M15a, gated by `compt i`)

- `wft_wf : lwf l → A @ l → Γ, A ⊢ N : Nat @ 0 → Wf^l(A; N) @ l`;
- `eqty_wf : l ≡ l' → A @ l → A ≅ A' @ l → Γ, A ⊢ N ≅ N' : Nat → Wf ≅ Wf' @ l`;
- `wf_supf : … → a : A @ l → cs : Vec^l(Wf; N[a]) @ l → sup_f : Wf @ l`;
- `wf_elimWf`, with the telescope's types (`wfcsty`, `wfihty`) as premises
  so that inversion returns them, as `wf_elimW`;
- the congruences `eqtm_supf`, `eqtm_elimWf`;
- β, `eqtm_elimWf_supf`, at a `sup_f` carrying the eliminator's own
  annotations; β at other annotations follows from injectivity of `Wf`
  (as `RS_elimW_sup`).

## The relation (design point)

MX §11's type rule is `W`'s with a term relation at `Nat` in place of the
position-type relation. So `LRwf` keeps `W`'s domain family `domR` and
replaces `codR` by a fixed premise: in every world, related shapes give
related arities, `NatRel (ktml ρ N)[a] (ktml ρ N')[a']`. The term relation
is MX §12's `NfEqWf`, a finitary Kripke induction over a Σ-spine. It is
three mutual families, indexed (as `WRel`) by the context, the level, the
left side's `A` and `N`, and `domR`:

- `WfRel`: both sides reduce, at the left `Wf`, to whnfs related
  generically and by `WfNf`.
- `WfNf`: two `sup_f`s whose annotations agree with the type's, whose
  shapes are related in every world (as `WNf`), and whose children are
  related **in every world** by the spine at the two arities
  `(ktml ρ N)[ktm ρ a]` and `(ktml ρ N)[ktm ρ a']`; or two neutrals,
  related generically.
- `VecSp k k' cs cs'`: the term relation at `Vec^l(Wf; k)`, as the M14a
  relation builds it, by cases on how the two lengths reduce
  (MX §12's table):
  - both to `0`: `UnitRel` (`Vec ⇝ Unit`, irrelevant);
  - both to `succ m`, `succ m'` with `NatRel m m'`: the children reduce at
    `Σ^{l,l}(Wf). Vec^l(Wf↑; m↑)` to whnfs related generically at both
    sides' `Σ`, their first projections are related by `WfRel` and their
    second by `VecSp m m'`, for every choice of equivalent annotations
    on the projections (as `SigRel`);
  - both to neutrals: `NeRel` at `Vec^l(Wf; ν)` (a neutral type).

Three choices, each forced by a proof that uses it:

1. **The spine is the relation at `Vec`, spelled out, not a premise
   `LR … (tyVec …)`.** A type derivation at `Vec(Wf; k)` contains the
   one at `Wf` being defined, so it cannot be a premise of the `Wf` case.
   Coq accepts `SigRel` itself nested in the spine (checked), but the
   generated `Scheme` gives no induction hypothesis through the nesting,
   and `elim_Wf` needs exactly that one. The fst and snd premises are
   therefore separate, which is `SigRel` with its existential split (its
   codomain does not depend on the first component, M14a's
   `vec_cod_single`). Two bridge lemmas relate the spine to the term
   relation of any type derivation at `Vec(Wf; k)`, by induction on the
   length's `NatRel`: spine to relation (for `elim_Wf`'s step argument)
   and relation to spine (for `sup_f`'s validity).
2. **The spine's projections are at its own world; the `sup_f` premise is
   Kripke.** MX §12(2) wants the children Kripke-quantified because §13
   and §14 apply them under a weakening: the induction hypothesis
   `λ` is a `Π` whose relation quantifies over worlds. Putting the
   quantifier at the `sup_f` (as `WNf`'s children) gives the induction
   hypothesis at every world, read straight off the derivation; the
   spine below it then needs no identity world when the index lemma
   descends into `fst` and `snd`. The spine's weakening is a lemma,
   mutual with `WfRel`'s.
3. **Only the left side's `A` and `N` index the families** (as `WRel`):
   the right side's children are typed at the left `Vec`. Symmetry and
   transitivity move a derivation to the other side's data through one
   transport lemma (generically equal `A`, `N`, pointwise equivalent
   `domR`), as M13a's `WRel` lemmas do.

The relation's lemmas mirror `W`'s, each with the spine as a third mutual
family: escape (`WfRel` stores the generic equality), symmetry (`NatRel`
is symmetric, so the spine mirrors), transitivity (the composite spine
recursion MX §15 flags: compose by induction on the first spine and
inversion of the second, whose length and children reduce to the same
whnfs by determinism), weakening, level invariance and universe
permutation.

## The index lemma (design point)

MX §13: `elim_Wf`'s arm needs relatedness at arbitrary `Fin` indices,
which the finite spine does not hand over directly. In Coq it splits in
two.

- **`LR_nth`, for any element type.** For `T` related, `k ~ k'` at `Nat`,
  `cs ~ cs'` at `Vec(T; k)` and `i ~ i'` at `Fin(k)`,
  `nth(T; k; cs; i) ~ nth(T'; k'; cs'; i')` at `T`. By induction on
  `NatRel k k'`, at every world (the neutral-index case compares the
  `case`'s right branch under its binder `j : Fin m`, a weakening). The
  four cases are MX §13's: at `0` the index is a neutral of `Empty` and
  `nth` reduces to `elim_Empty`; at `S m` an `inl` index gives `fst cs`,
  an `inr j` gives `nth(T; m; snd cs; j)` (syntactically, up to
  substitution lemmas: `nth`'s recursive call is `nth` at the
  predecessor), and a neutral index gives a neutral `case`; at a neutral
  length `nth` is a neutral `natrec` under two applications.
- **The spine motive in `elimWf_core`.** `elim_Wf` is valid by induction on
  `WfRel`/`WfNf`/`VecSp` (as `elimW_core` on `WRel`). The spine's motive
  is: for every relation at `Fin(k)` and indices related by it, the two
  eliminations at `nth(Wf; k; cs; i)` are related. `inl` uses the `fst`
  premise's induction hypothesis, `inr` the `snd` spine's; every neutral
  case gets `nth ~ nth` at `Wf` from `LR_nth`, whose whnfs are then
  neutral (determinism), and `elim_Wf` of a neutral needs no induction
  hypothesis. This is MX §13's "witnessed by a subderivation".

At a `sup_f`, both sides step to the step at the shape, the children and
`wfIH`. The children are related at `Vec(Wf; N[a])` by the spine-to-
relation bridge; `wfIH` is a `λ` whose applications at related indices
step to the eliminations at `nth`, related by the spine's motive. No
funext appears: the only `Π` is `wfIH`'s, related through its
applications (MX §14).

## Algorithm

`Wf` is `posty`: two `Wf` types compare by level, shapes by `ac_ty`,
arities by `ac_tm` at `Nat` under the shape binder (`actynf_wf`); two
`sup_f`s by shape at the left shape type and children at the left
`Vec(Wf; N[a])` (`actmnf_supf`), so the children comparison descends
through `Vec`'s reduction to `Σ`'s and `Unit`'s, with no `Wf`-specific η
(MX §16); `elim_Wf` is a neutral whose step is compared in the left side's
telescope at the left side's step type (`actmne_elimWf`).

## Consequences to extend

Canonicity (a closed term of `Wf` computes to a `sup_f`), the head table,
preservation (`RS_elimWf`, `RS_elimWf_supf`), type uniqueness,
consistency (`neutral_univ`) and type checking (`dec_tyWf`, `sy_supf`,
`sy_elimWf`).

## The four recursor branches, derived from the rules (M15b)

`uncovered-formers-recursor-rules` asks for the `Wf` group's `G_Typ`/
`G_Trm` bindings written from the semantics. A branch's scope is fixed by
its code's typing rule at layer C: one universe binder per level the
former's annotations carry, one global per component (a `Typ` binding for
a type component, a `Trm` binding for a term component, each in the local
context and at the level the rule types the component), and one local per
global, the recursive call at the motive of the global's sort, at the
binding's context, type and level. Read off the rules above (M14b's
notation; `g : Ctx` first):

- **`t_Wf`** (type motive), `(1, 3, 2)`: `ℓ`; `U_S : Typ_c(g, ℓ)` (the
  shape is a type at `ℓ`), `u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0)`
  (the arity is a `Nat` term under the shape's binder, at level 0); calls
  `x_S` at the type motive (`g`, `ℓ`) and `x_n` at the **term** motive
  (`(g, x : U_S^id)`, `Nat`, level 0). Head `M_Typ` at `ℓ`, scrutinee
  `box (Wf^ℓ(x : U_S^id). u_n^id)`. One universe, not `W`'s two: the
  arity carries no level.
- **`t'_Wf`** (term motive, the code), `(1, 3, 2)`: `u_s : Trm_c(g ⊢ Ty ℓ
  @ 1+ℓ)`, `u_n : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Nat @ 0)`; calls `x_s`
  (term motive, `Ty ℓ`, `1+ℓ`) and `x_n` (term motive, `Nat`, 0). Head
  `M_Trm` at `1+ℓ`, `Ty ℓ`.
- **`t_supf`**, `(1, 5, 4)`: `U_S`, `u_n` as `t_Wf`'s;
  `u_a : Trm_c(g ⊢ U_S^id @ ℓ)`;
  `u_cs : Trm_c(g ⊢ Vec^ℓ(Wf^ℓ(x : U_S^id). u_n^id; u_n^{id, u_a/x}) @ ℓ)`
  (`wf_supf`'s children premise, the arity at the shape). Calls: `x_S`
  at the type motive (`ℓ`), `x_n` at the term motive (0), `x_a` and
  `x_cs` at the term motive (`ℓ`, at those types). Head `M_Trm` at `ℓ`,
  type `Wf`.
- **`t_elimWf`**, `(2, 6, 5)`: `ℓ, ℓ'`; `U_S`, `u_n` as above;
  `U_M : Typ_c((g, z : Wf @ ℓ), ℓ')`;
  `u_s : Trm_c((g, a : U_S^id @ ℓ, cs : wfcsty @ ℓ, ih : wfihty @ 0⊔ℓ')
  ⊢ U_M^{…, sup_f(a; cs)/z} @ ℓ')`, the step telescope above with `U_M`
  for `M`; `u_t : Trm_c(g ⊢ Wf @ ℓ)`. Calls: `x_S` and `x_M` at the
  **type** motive (`ℓ` in `g`; `ℓ'` in `(g, z : Wf)`), `x_n` at the term
  motive (0), `x_s` at the term motive (`ℓ'`, the step type), `x_t` at the
  term motive (`ℓ`, `Wf`). Head `M_Trm` at `ℓ'`, type `U_M^{id, u_t/z}`.

Checked against `H/crates/kernel/src/rec.rs` (`ty_wf`, `tm_wf`, `tm_supf`,
`tm_elim_wf`) at Heather `b5b2b9d`: they agree slot for slot — the
universe counts, every global's sort, context, type and level, every
local's motive and level, and the heads. The four type-motive slots the
issue lists for this group (`ty_wf`'s `x_S`, `tm_supf`'s `x_S`,
`tm_elim_wf`'s `x_S` and `x_M`) are the ones derived above. One
difference is spelling only: `rec.rs` (and `typing.rs`) declare `ih` at
`ℓ'` where ours writes `0 ⊔ ℓ'`; Heather's levels are normalized, so the
two are the same level. M15b's `rec_code` will validate these bindings
as M14b's did `ty_vec`'s.

## M15a outcome (2026-10-06)

Done at layers D and M. Every headline theorem stays closed under the
global context: `Print Assumptions` of `wf_tm_dec`, `closed_canonicity`,
`ac_tm_sound`, `V_elimWf` and `V_elimWf_supf` lists nothing, so the
design's "no funext" holds.

- **Syntax, typing, reduction** as designed: `tyWf`, `tmSupf`,
  `tmElimWf`, `tmNth` and `wfIH` (definitions, so every syntax operation
  pushes through them by lemma: `gren_tmNth`, `gwa_tmNth`, …), the step
  telescope as the notations `wfcsty`, `wfihty`, `wfstepty`.
  Presupposition gains the telescope's typing (`Wf_cs_wf`, `Wf_nth_wf`,
  `Wf_ih_wf`, `Wf_step_wf`) and its congruences (`Wf_ih_eq`,
  `Wf_step_eq`), and `nth_wf`/`nth_eq` type `nth` from its schema.
- **The relation** is the three mutual families designed (`WfRel`,
  `WfNf`, `VecSp`; `Validity/Wf.v` and `LogRel/Def.v`), with escape,
  symmetry, transitivity, weakening, level invariance and universe
  permutation each gaining the spine as a third mutual family. Injectivity
  of `Wf` (`Wf_inj`, and its D/M instances `decl_Wf_inj`,
  `declM_Wf_inj`) comes from `LR_inv_wf`, as `W_inj`.
- **The index lemma departs from the design in method, not statement.**
  The design proves `LR_nth` by induction on `NatRel k k'`. Instead,
  `nth` is a fixed `natrec` schema, so `V_nth` (`Validity/WfNth.v`) is
  the composition of the validity lemmas of the formers it is built
  from (`natrec`, `λ`, application, `case`, `elim_Empty`, the
  projections, `Vec`'s and `Fin`'s computation rules) along `nth_wf`.
  Composition needs the lemmas closed under global weakenings, so
  `WfNth` lifts the ones it uses to `VTyG`/`VTmG` form (`VG_*`). The
  four reduction cases of MX §13 then reappear only as untyped
  computations (`nth_reds_inl`, `nth_reds_inr`, `nth_reds_case_ne`,
  `nth_reds_zero`, `nth_reds_ne`), which the eliminator's motive needs.
- **The spine motive is stated by reduction, not syntax.** At a length
  `k`, a tuple `cs` and related indices, the motive covers *any* two
  terms related at `Wf` that reduce to `nth(cs; i)` and `nth(cs'; i')`
  (`reds`). Stating it at `nth` itself fails at `inr`: the predecessor's
  `nth` is `nth`'s reduct only up to substitution lemmas, and the
  motive must survive that. `elimWf_core_all` is one induction
  (`WfRel_comb`) over the three families with motives `elimWf_mrel`
  (twice) and `elimWf_mspine`.
- **At a `sup_f`** (`elimWf_step`): the children are related at
  `Vec(Wf; N[a])` in the step's world by `LR_of_VecSp_own` (the
  spine-to-relation bridge at the identity world), and `wfIH`'s
  applications at related indices by `elimWf_nth_kw`, the `nth` at a
  Kripke world related at `Wf` (from `V_nth`), fed to the spine motive.
- **Validity and the fundamental theorem**: `V_wf`, `V_supf`,
  `V_elimWf`, `V_elimWf_supf`, with `VS_*` forms in `RulesS`. Two
  mechanical changes: `gwa_tmNth` and `gwa_wfIH` moved from `WfElim` to
  `GLift`'s push table (`VS_elimWf`'s `s_lift` must push `⟦γ⟧` through
  `nth`), and `FundamentalM`'s second `us_rewrite` pass also triggers on
  `tyWf` (an unpushed `usubst_tm N[lsingle a] φ` otherwise remains).
- **Algorithm** as designed: `actnf_wf`, `actmnf_supf`, `actmne_elimWf`
  through soundness (`Wf_ctx_conv` moves the right step into the left
  telescope, `elimWf_step_left`), conversion, symmetry and transitivity
  (`Wf_tele_eq`, `wf_cs_conv`; `ainv_wf`, `ainv_supf`, `ainv_elimWf`),
  lifting, the `AlgEq` laws (`geq_ty_wf`, `geq_tm_supf`,
  `gne_tm_elimWf`) and decidability. `elim_Wf` joins the neutral-head
  tables (`ne_head`, `is_whne`, `tm_con`).
- **Consequences**: closed canonicity gives a `sup_f` at `Wf` (head 18),
  preservation (`RS_elimWf`, `RS_elimWf_supf`, β at any annotations by
  `Wf_inj`), `neutral_univ` (consistency), type uniqueness
  (`inva_supf`, `inva_elimWf`) and type checking (`dec_tyWf`, `sy_supf`,
  `sy_elimWf`, deciding `compt i` first).
- **Gotchas**: in `TCSynth`, `compt_notV` names a different lemma than
  in the algorithm files, so `i <> lV` is derived by cases on
  `compt i`. `Wf_Na_eq` takes `Hi` but not `Hv`, unlike its neighbours;
  check `About` before applying a section lemma by position.

**Cost.** 66 files, about 6350 lines added, about 2100 of them in the
three new validity files (`Wf.v`, `WfNth.v`, `WfElim.v`) and 870 in
presupposition. A clean `make -j2` took 875 s wall on
the 2026-10-06 cloud machine of this round (critical path 740 s, total
CPU 1106 s); M14b measured 584 s on another machine, so the two do not
compare directly.

## M15b outcome (2026-10-10)

Done in two commits, on M13b's and M14b's pattern, after step 0. Every
headline theorem stays closed under the global context (`Print
Assumptions` of `wf_tm_dec`, `wf_ty_dec`, `consistency`,
`closed_canonicity`, `paper_sound`, `rec_red_typed`,
`subject_reduction_tm`, `subject_reduction_ty`, `RecS.rec_code` and
`V_elimWf` lists nothing).

- **Step 0, the genericity pass** (HEATHER.md, direction 1; its outcome is
  recorded there). `derived_calls` computes a branch's recursive calls
  from `brDecls` (one per layer-C global, weakened past its position) and
  `br_calls_derived` checks the written `br_calls` and `br_nl` against it
  for all 51 branches. `GSall`/`GS_br` fold `GSubRel` over `brDecls`
  (`GWall`/`GW_br` fold `gsub_wf` in `RecReduct`), and `RTcall`/`Rtcall`
  give a call's typings, conversion and relation from its induction
  hypothesis. The existing branches are not migrated.
- **Step 1, the code at D and M**: `tmWf l s n : Ty l` (the arity is a
  `Nat` term under the shape's `El` binder, so the code lives at the
  shape's level), `El (Wf^l(x : s). n) ⇝ Wf^l(x : El s). n`, structural
  code equality, and every lemma family as for the other codes.
- **Step 2, the lift to C**: `wft_wf`, `wf_supf`, `wf_elimWf`,
  `wf_code_wf` and their congruences take `i <> lV`; β and the decoding
  stay at `compt i`. `nth` has no layer-generic typing in
  `Presupposition` (its `case` on `Fin (S k)` and its pair at `Vec(S k)`
  are typed through `Fin`'s and `Vec`'s computation rules), so
  `StaticCode` ports `nth_wf` and the step telescope's typing to every
  layer but V (`nth_wf_g`, `Wf_cs_wf_g`, `Wf_ih_wf_g`, `Wf_step_wf_g`),
  with contexts at `typeof i` and those conversions through `wf_conv`
  at `typeof i`, as the design's syntax section anticipated. The type
  checker's `elim_Wf` at C builds its premises from them. Static code
  (`sc_wf`, `sc_supf`, `sc_elimWf`, `sc_code_wf`, with `_q` forms for
  the callers that already hold both sides' typings; `sc_elimWf_q`
  types the right telescope from its own components through `WfGen`,
  which replaced a first version that converted the left telescope's
  typing along `ty_leq` and cost `StaticCode` about 10 s)
  and PresupC (`pc_wf`, `pc_supf`, `pc_elimWf`, `pc_codewf`) gain their
  cases; the algorithm and preservation reach the lifted rules through
  `compt_notV`.
- **The four branches** are 47–50 (`nbr = 51`), at the scopes derived
  above (`brDecls`), which `rec_code` now validates: `t_Wf`, `t'_Wf`,
  `t_supf`, `t_elimWf`. Their scopes are typed by `RecWf`'s memoised
  automation (as W's; the selector is now `39 <= k < 43 || 47 <= k < 51`),
  which gains `nth`'s formers and the three conversions its unfolding
  crosses (`wconv`). `RecS` has the reduct instances, the push lemmas for
  the telescope notations (`us_/gs_wfcsty`, `wfihty`, `wfstepty`) and one
  lemma per branch (`RT_wf`, `Rt_codewf`, `Rt_supf`, `Rt_elimWf`);
  `RecReduct` has `rr_T_wf`, `rr_t_codewf`, `rr_t_supf`, `rr_t_elimWf`
  and the `C_*` entries.
- **Gotchas.** (1) `-vos` checks a section proof only when it lacks
  `Proof using`, and never a proof outside a section: a push lemma that
  passed `-vos` failed the full build. (2) `AlgPrereq`'s `br_tac` typed
  `elim_Wf`'s step scope (Γ, a, cs, ih) afresh at each of six goals, about
  6 s each since the `ih` entry carries `nth`; `br50_pre` types it once
  as hypotheses in the form those goals take, after `br_prep` (whose
  `destruct ... in *` would otherwise take them apart). `RecAdm`'s
  `brΓ_wf`/`brRes_wf` had the same cost (36 s → 145 s) and get the same
  fix (`wf50_pre`, 67 s): context well-formedness is memoised only
  through `assumption`, so one pre-asserted step context serves every
  goal that mentions it. (3) `AlgPER`
  redefines `compt_notV` with `i` implicit, so a proof script shared
  with the files before it writes `apply compt_notV; exact Hc`.

**Cost.** Step 1: 32 files, about 450 lines (commit "M15b step 1").
Step 2 with step 0: 29 files, about 1530 lines added; `StaticCode` 410
(the layer-generic `nth`), `RecS` 500 and `RecReduct` 190, of which about
200 are the generic infrastructure (HEATHER.md has the abort criterion's
count). **Build time.** A clean `make -j2` took 887 s wall on the 2026-10-10
cloud machine (critical path 732 s, total CPU 1125 s), where the M15a
tree measured 689 s wall the same day (critical path 655 s, CPU 971 s):
critical path +77 s (+12%), CPU +154 s. The new branches carry most of
it: `RecAdm` +36 s (branch 50's step scope, already halved by
`wf50_pre`), `AlgPrereq` +23 s (`br50_pre` itself 13 s, then 23 s for
the branch goals), `RecS` +12 s and `RecReduct` +6 s (the four reduct
lemmas), `RecWf` +6 s (`nth` in the memoised automation), `StaticCode`
+6 s (`WfGen`). `LevelRed` +12 s is its constructor-injection loop
growing with the three new term formers. Step 0's generic lemmas take about
2 s of `RecS`; `br_calls_derived` is under 0.1 s.

