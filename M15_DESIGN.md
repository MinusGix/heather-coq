# M15: finitary well-founded trees (`Wf`), design

Status: **M15a in progress** (2026-10-06). Why now: `HEATHER.md` item 5
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
