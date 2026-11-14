# M19: indexed families with infinitary children (`IWi`), design

Status: **done** (2026-11-14): M19a, M19b ("M19b outcome" below; the
algorithm, decidability, the type checker and canonicity followed it)
and M19c ("M19c outcome").

`IWi` is `IWf` (M17b) whose children are functions: a constructor has a
finite tuple of recursive fields, and field `i` is a function from its own
domain `D[a, i]` into the family. It is the kernel former for Heather's
`k: (y: A) -> D(e)` fields in an indexed family, today lowered to `W` plus
two stored equations (Heather's `docs/iwf-infinitary-design.md` §3). The
choice of this form over a single position type (indexed `W`, `M`'s
inductive dual) is argued in "Why a tuple of functions" below; the
background (risks, gains, the pruning probe) is
`PRUNE_VEC_WF.md` and the write-up linked from it.

## Why a tuple of functions

- **No stored equations.** `IWf`'s constructor sits at its index, so the
  index equation goes, as for `IWf`. A single position type packs a
  constructor's fields into a sum `A₁ + … + Aₙ`; a `match` arm's
  constructor form rebuilds the children function from the fields, which
  is convertible with the scrutinee's only with η for sums (or for
  `Empty`, at no fields). The kernel has neither, so the children equation
  (and the stored copy `k̄` of the fields, and a second `J` in `match`)
  would stay. A tuple has a component per field and η per component (Σ's
  and `Unit`'s), so nothing is rebuilt.
- **One to one with the surface.** A constructor's recursive fields are
  the tuple's components, in order; a plain child is a function from
  `Unit`.
- **Runtime.** A value is a shape and a Σ-chain of closures; a field at a
  literal position is `fst`/`snd` steps and an application. The cost is a
  closure for a plain child of a constructor that has a function field.
  Families without function fields stay on `IWf`, so ordinary data pays
  nothing.
- **Metatheory.** It combines `IWf`'s spine (`DVecISp`, `dnth`) with
  `W`'s Kripke children premise (`WNf`) per component. More than indexed
  `W` alone, paid once.

Kept as defaults (no fork): index-last as `IWf` (the constructor's index
is computed from its shape, `Ot[a]`); `IWf`, `W` and `Wf` stay formers
(folding them into `IWi` is `PRUNE_VEC_WF.md`'s question again, left open).

## Syntax (M19a)

Appended after `M`'s constructors, with `IWf`'s binder conventions:

- `tyIWi l lp li X A N D Ot C m`: `X` the index type at `li`; `A` the
  shapes at `l`; under `x : A` the arity `N` and the output index `Ot`;
  under `x : A, i : Fin N` the domain `D` at `lp`; under
  `x : A, i : Fin N, y : D` the child index `C`; the index `m`.
- `tmSupii l lp li X A N D Ot C a cs`;
- `tmElimIWi l lp li l' X A N D Ot C M c m t`, `M` under `j : X,
  z : IWi(j)`, `c` under `a, cs, ih`;
- the code `tmIWi l lp li x s n d o c m` (M19c).

Levels: the type lives at `iwiL l lp li := lmax (lmax l li) lp`.

Definitions (as `iwfFam`, `iwfIH`):

- `iwiFam a` (in `Γ, k : Fin N[a]`): `Π^{lp, L}(y : D[a, k]). IWi(…)(C[a, k, y])`,
  the type of field `k`, with `L := iwiL l lp li`.
- children: `DVec^L(N[a]; k. iwiFam a)`.
- `iwiIH c a cs := λ(i : Fin N[a]). λ(y : D[a, i]).
  elim_IWi(…; C[a, i, y]; app(dnth^L(N[a]; iwiFam a; cs; i), y))`.

Reduction: `red_elimIWi_supii` (β, below) and the congruence on the
scrutinee; `whne_elimIWi` at a `whne` scrutinee. No type reduction: `IWi`
is a whnf.

## Rules (M19a; `i <> lV`, β at `compt i`)

```
wft_iwi : X @ li, A @ l, (x:A) ⊢ N : Nat, (x:A, i:Fin N) ⊢ D @ lp,
          (x:A) ⊢ Ot : X, (x:A, i:Fin N, y:D) ⊢ C : X, m : X
          ⊢ IWi^{l,lp,li}(X; A; N; D; Ot; C)(m) @ iwiL l lp li

wf_supii : (the signature), a : A, cs : DVec^L(N[a]; k. iwiFam a)
          ⊢ sup(a; cs) : IWi(…)(Ot[a])

wf_elimIWi : (the signature), (j:X, z:IWi(j)) ⊢ M @ l',
          (a, cs, ih : Π^{0}(i : Fin N[a]). Π^{lp}(y : D[a,i]).
                         M[C[a,i,y], app(dnth(cs; i), y)]) ⊢ c : M[Ot[a], sup(a; cs)],
          m : X, t : IWi(m)
          ⊢ elim(…; M; c; m; t) : M[m, t]

β (compt i):  elim(…; Ot[a]; sup(a; cs)) ≅ c[a, cs, iwiIH c a cs]
```

with the congruences `eqty_iwi`, `eqtm_supii`, `eqtm_elimIWi` as
`IWf`'s (typed eliminator congruence, `ELIM_CONGRUENCE.md`: the step's
telescope types as premises, as `wf_elimIWf` states them). No η.

## The relation (M19b)

`LRiwi` is `LRiwf` plus a domain family: `idxR` (the index type, in every
world), `domR` (the shapes), and `posDomR`, the relation at `D[a, i]` for
related shapes and related positions (`PosRel`), in every world, as `W`'s
`codR` is over `domR`. The term relation is `IWf`'s three mutual
families with the index as an index:

- `IWiRel m t t'`: whnfs related generically and by `IWiNf m`;
- `IWiNf m`: two `sup`s whose annotations agree with the type's
  (`IWiEq`), shapes related in every world, `Ot[a]` related to `m` at `X`,
  children related by the spine in every world; or two neutrals;
- `DVecWSp c k cs cs'`: `DVecISp` with its head clause replaced by
  `WNf`'s children premise: the heads reduce, in every world, to whnfs
  related generically at `iwiFam`'s `Π` (as `PiRel`'s first clauses), and
  for related `y ~ y'` at `D[a, hd]` their applications (at any
  equivalent annotations) are related by `IWiRel` at `C[a, hd, y]`. The
  tail is the spine at the moved families (`posMv` on both `C` and `D`).

`elim_IWi`'s validity is `elim_IWf`'s induction over the three families;
the induction hypothesis at a field is a `λ` over `y` (as `elim_W`'s),
built from the spine's head premise. The child index `C[a, i, y]`
depends on `y`, so relating two children's indices needs `C`'s validity
at related `y ~ y'`, which the signature's premises give, as `M18b`'s
child index did.

## M19b outcome (validity)

Files, in dependency order, beside `IWf`'s:

- `LogRel/IWiAux.v`: the syntax in Kripke worlds, the signature in a
  world (`IWiSig`), the field types generically equal. `IWi`'s cases of
  symmetry, transitivity, weakening, neutral reflection, level invariance
  and universe permutation sit in their files beside `IWf`'s.
- `Validity/IWi.v`: formation and `sup_ii`; the canonical relations
  (`IWiCan`) and applications of terms related at `Π`.
- `Typing/IWiIH.v`: the synthesized induction hypothesis `iwiIH`, typed.
  It is a `λ` under two binders (the field index and the position), so
  validity needed `LRtm_lam2_K`, a `λ`-introduction under two binders in
  every world.
- `Validity/IWiSp.v`: the converse of `DVecWSp_of_LR`. A `sup_ii`'s
  spine, in every world, is related at its `DVec` (`LR_of_DVecWSp_own`),
  through `YOk` (a child's relation at a position) and `IKSpW` (the spine
  at a Kripke weakening).
- `Validity/IWiElimBase.v`, `IWiElimDnth.v`: the step telescope under
  weakenings and substitutions, the positions an index of `Fin` reaches,
  and the children's `dnth` valid, as `IWfElim`'s `elimIWf_Vdnth`.
- `Validity/IWiElim.v`: `elim_IWi`'s validity. `elimIWi_ann` relates
  the field annotations at related positions; `elimIWi_kgoal` is the
  induction hypothesis's body in a world, at related positions `y ~ y'`
  (the one part `IWf` has no counterpart for); `elimIWi_step` is the
  step at `sup_ii`; `elimIWi_core_all` is the induction over `IWiRel`,
  `IWiNf` and `DVecWSp`. `V_elimIWi`, its type and β follow.
- `Validity/RulesSIWi*.v`: the lifted rules for `FundamentalS`, split as
  `RulesSIWf*` is so they build in parallel (`F` formation and `sup_ii`,
  the eliminator, its type, β and β's type).

No admits; no new axioms.

## M19c outcome (the code and layer C)

No admits; no new axioms. The code `tmIWi l lp li x s n d o c m`
decodes to `IWi(El x; El s; n; El d; o; c)(m)`; `IWi`, `sup_ii`,
`elim_IWi` and the code are typed at every layer but V (β stays at D and
M), and the code recursor has the four branches `t_IWi`, `t'_IWi`,
`t_sup_ii`, `t_elim_IWi` at 61–64 (`nbr = 65`). Staged in two commits,
as M17c:
- **The code at D and M, then the lift to C**: typing through the
  metatheory, validity (`Validity/IWiCode.v`), the algorithm and its
  decidability, canonicity, preservation and synthesis. The algorithm's
  code case compares the arities before the domains, so the right
  domain code, typed over the right shape and arity, moves into the left
  contexts (`IWi_d_mv`, AlgSound) before it is compared.
- **The branches**: reducts (`Syntax/Recursor.v`), scopes (`RecSpec`,
  levels `ℓ ℓp ℓi (ℓ')` bound in that order, checked by
  `br_calls_derived`), the laws (`RecLaws`, `SubstRec`, `RecLawsRedt`,
  `RecGSubst`, `GRenRedt`), the scopes' well-formedness (`RecWf`), their
  admissibility (`RecAdm`, with the eliminator's head typed in
  `Typing/WfScopeIWi.v`), the reducts' typing (`RecReductCases`,
  `AlgPrereq`) and the relation: `Validity/RecSIWi.v`, `RecSIWiCode.v`,
  `RecSIWiSupi.v`, `RecSIWiElim.v`, one lemma per branch, wired into
  `RecS`'s `rec_code` and building in parallel as `RecSIWf*` do.

Decisions and deviations, in the order the proof met them:
- **The scopes are derived, not transcribed.** Heather's `rec.rs` has no
  `IWi` branches yet; the four scopes are stated from the layer-C rules
  and are the reference Heather's are to be checked against. The
  domain's call `x_D` sits under the shape and a position, the child
  index's `x_C` under the domain too; `t_elim_IWi`'s calls exclude the
  step telescope's types, as `t_elimIWf`'s do.
- **`dnth`'s family instances, weakened once (DNthCore).** `IWi`'s
  family `F(j) = Π(d : D(a, j)). IWi(…)(C(a, j, d))` puts the index
  under a binder, so typing `dnth`'s steps needs each instance also at
  `t⟨↑⟩` in `Δ, X` for any `X`. `RecWf` runs before weakening exists
  (local weakening needs `GWeakening`, which needs `wf_brG`), so
  `DNthCore` takes these weakened instances as premises (`wk_tm`,
  `wk_eq`; `FW`, `FV`, `FE` and `FE0` carry them, and `NW`'s bound rises
  to 11 locals): `DNth` discharges them by weakening, and `RecWf`'s
  automation types them under the abstract binder (`wty_hyp`'s
  quantified hypotheses). The β steps' weakened instances come from
  `beta_wk`, the abstract index's from `wk_parts`.
- **The weakened instances normalise back to renamings.** `RecWfBase`'s
  `wnorm` computes `t⟨↑⟩` into `ren_tm`'s fixpoint; `wrefold` folds the
  unfolded fixpoint back to `ren_tm` so the quantified hypotheses match.
  The automation also gained `tyGvar` equations (`eqty_gvar`) and a
  conversion fallback (`wty_conv`) for the equality instances.
- **Globals under three binders.** The child index `X⟨↑⟩⟨↑⟩⟨↑⟩`: `rr_sh`
  (RecReductCases) and `AlgPrereq`'s `wf_gv_up3`/`wf_gu_up3T`, as M17c's
  under two.
- **Right payloads at the left levels**, as M17c's: the domain is
  related by `RTcall` along the shape's and the arity's context equation
  at the right levels, then moved to the left levels' context
  (`ctxconv_ty`); `IWiEq_intro` packs the signature's equations.

## Staging

- **M19a**: syntax, substitution and renaming laws, reduction, the typing
  rules and the typing metatheory (weakening, substitution, inversion,
  presupposition) at every layer but V, β at D and M.
- **M19b**: the relation, validity, the fundamental theorem, the
  algorithm, decidability, the type checker, canonicity (a closed term
  at `IWi` computes to a `sup`).
- **M19c**: the code `tmIWi`, its decoding, the lift to layer C and four
  recursor branches (`ty_iwi`, `tm_iwi`, `tm_sup_ii`, `tm_elim_iwi`),
  ahead of Heather's `rec.rs`.

Template: M17b (`IWf`) for every file; `W` (M13) for the children
premise; M18b (`M`) for an infinitary child index.
