# M17: indexed finitary trees (`DVec`, `IWf`), design

Status: **M17a done** (2026-10-13), **M17b done** (2026-10-14), **M17c done** (2026-10-14). Why now: Heather froze `IWf`'s
rule set (`H/docs/iwf-former-design.md` §1–§6, 2026-10-13), and `IWf` is
how its kernel loses `transp` and the strip: route 2b's indexed families
store an index equation that only `transp` can use, and `IWf` stores
none. Checking the rules here before Heather implements them is the
direction of authority `HEATHER.md` asks for (it is how Empty-η went), and
it answers the one question the freeze left to this repo: the ih's type
is `F[i]` only up to β (doc §3), one step more than `V_nth` (M15a)
needed.

Heather's rules: `H/docs/iwf-former-design.md` §§1–6 (doc below),
`H/issues/iwf-former.md`. No kernel code exists yet, so the de Bruijn
transcriptions here (`dnth` above all) are the first precise statement
of them, and Heather's later `typing.rs`/`reduce.rs`/`rec.rs` are to be
checked against them, not the other way round.
- `DVec^l(k; i. F) @ l`, for `k : Nat @ 0` and `F @ l` over
  `i : Fin k`: `Vec` with a per-position element type. Computes on a
  canonical length:
  - `DVec^l(0; i. F) ⇝ Unit^l`;
  - `DVec^l(S k; i. F) ⇝ Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec^l(k; j. F[inr j/i])`;
  - neutral at a neutral length; no η of its own.
- `dnth^l(n; i. F; cs; i)`, derived, not a former (doc §3): a `natrec`
  on the length whose motive quantifies over an embedding
  `e : Fin k̂ → Fin n`, applied to the identity embedding.
- `IWf^{l,li}(I; x:S. n; x. o; x i. c)(m) @ l ⊔ li`, `sup_i`,
  `elim_IWf`, β at a `sup_i` on open data, no η (doc §§1.2, 2, 4, 5).
- Codes `TmDVec`, `TmIWf` and six recursor branches (`ty_dvec`,
  `tm_dvec`, `ty_iwf`, `tm_iwf`, `tm_sup_i`, `tm_elim_iwf`; doc §6).

`DVec`/`IWf` land as siblings of `Vec`/`Wf` (doc §10, option 1; recorded
in `HEATHER.md`): `Vec^l(T; k)` and `DVec^l(k; _. T)` agree reduct for
reduct at a canonical length and are distinct neutral types at a neutral
one, so no conversion between the two pairs is stated or wanted.

Gating follows M13–M16: the formers at layers D and M first (`compt i`),
then every layer but V with the codes.

## Staging

- **M17a**: `DVec` and `dnth` at layers D and M. `DVec` through every
  consequence, as M14a's `Vec`; `dnth`'s typing (`dnth_wf`) and its
  validity (`V_dnth`), the index lemma `elim_IWf` will need. No code.
- **M17b**: `IWf`, `sup_i`, `elim_IWf` and β at layers D and M, through
  the logical relation, validity, the algorithm, decidability and the
  consequences. M15a is the template.
- **M17c**: the codes, the lift to layer C (`dnth`'s typing ported as
  M15b ported `nth`'s, `nth_wf_g`) and the six branches 55–60, their
  scopes derived from the typing rules before `rec.rs` has them.

**No separate relation probe** (a departure from the ranking in the
project notes, which proposed one before M17a). The probe's question was
whether `dnth`'s index lemma survives the extra β. `dnth` is a fixed
schema over formers that all have validity lemmas, so its index lemma is
`V_dnth`, proved in-tree in M17a by M15a's method (`V_nth`, composition
along the typing derivation) at no more cost than a probe would take.
The other half of the probe, `IWf`'s relation with the index, is designed
below and checked by M17b itself; it has no question a probe would answer
earlier, since the relation is `Wf`'s with an index argument.

## Syntax (M17a)

- `tyDVec l n F`: `DVec^l(n; i. F)`, `F` under one binder (`i : Fin n`).
  Appended to `ty` after `tySq`.
- `tmDNth l n F cs i`, a definition (as `tmNth`): see below.

Reduction extends `red_ty`:
- `red_dvec_zero l F : tyDVec l zero F ⇝ tyUnit l`;
- `red_dvec_succ l n F : tyDVec l (succ n) F ⇝ tySig l l (dvecHd n F) (dvecTl l n F)`,
  with `dvecHd n F := F[inl^{0,0}(Unit^0; Fin n; ⟨⟩^0)/i]` in `Γ`, and
  `dvecTl l n F := DVec^l(n↑; j. F⟨⇑↑⟩⟨⇑↑⟩[inr^{0,0}(Unit^0; Fin n↑↑; j)/i])`
  in `Γ, x`, where `⟨⇑↑⟩` (`rlift ↑`) weakens `F` past `x` and then past
  `j` while keeping `i` innermost. The injections carry `Fin`'s reduct's
  annotations (`Fin(S n) ⇝ Unit^0 + Fin(n)`), so the head and the tail are
  at `F`'s family at a well-typed index without a conversion.
- `red_dvec l n n' F : n ⇝ n' → tyDVec l n F ⇝ tyDVec l n' F`.

`whne_ty` gains `whne_tyDVec` at a `whne` length. Determinism holds as for
`Vec`.

## Rules (M17a, gated by `compt i`)

- `wft_dvec : lwf l → n : Nat @ 0 → Γ, Fin n @ 0 ⊢ F @ l → DVec^l(n; F) @ l`;
- `eqty_dvec : l ≡ l' → n ≅ n' : Nat → Γ, Fin n ⊢ F @ l → Γ, Fin n ⊢ F ≅ F' @ l → DVec ≅ DVec' @ l`;
- `eqty_dvec_zero : lwf l → Γ, Fin 0 ⊢ F @ l → DVec^l(0; F) ≅ Unit^l @ l`;
- `eqty_dvec_succ : lwf l → n : Nat → Γ, Fin (S n) ⊢ F @ l →
  DVec^l(S n; F) ≅ Σ^{l,l}(dvecHd n F). dvecTl l n F @ l`.

As for `Vec`, the `Σ` reduct lives at `l ⊔ l` and is stated at `l`. The
reduct's typing (presupposition) instantiates `F` at `inl ⟨⟩` and at
`inr j`, both typed at `Fin(S n)` through `Fin`'s computation rule.

## The relation: no new case

As `Vec` (M14a): every type case is closed under typed weak-head
expansion, so `DVec` at a length reducing to `0` is `Unit`'s case, at
`S k` `Σ`'s, at a neutral length a neutral type. The fundamental theorem
builds it by induction on the length's `NatRel`, but, unlike `Vec`, the
family moves along the recursion (`F` at the successor, `F[inr j]` at the
predecessor), so the induction is generalized over a *semantic family*:

`DFam m m' F F'` := in every Kripke world `ρ`, for every `i ~ i'`
related at `Fin(m)` (`LRtm`, so whichever derivation of `Fin`'s
relation), `F⟨ρ⇑⟩[i] ~ F'⟨ρ⇑⟩[i']` are related types; plus `F`'s and
`F'`'s typings.

- `LR_dvec_nat : NatRel m m' → ∀ F F', DFam m m' F F' → LRty (DVec l m F) (DVec l' m' F')`.
- At `S k`, `Σ`'s domain is `F[inl ⟨⟩]`, from `DFam` at `inl ⟨⟩ ~ inl ⟨⟩`;
  its codomain in every world is the induction hypothesis at the family
  `F[inr j]`, whose `DFam` comes from `DFam`'s at `inr j ~ inr j'`,
  related at `Fin(S k)` by `+`'s case.
- At a neutral length, `gne_ty_dvec` needs `F ≈ F'` under `i : Fin ν`:
  `DFam` at the weakening by `Fin ν` and `var 0 ~ var 0`, then escape.
- `V_dvec` turns `VTy (Γ, Fin n) F F'` into `DFam` at related
  substitutions, as `V_pi` turns its codomain's validity into the
  codomain relation.

The generic equivalence gains one neutral-type law, `Vec`'s with a
binder:
`gne_ty_dvec : l ≡ l' → ν ~ ν' : Nat @ 0 → Γ, Fin ν ⊢ F @ l → Γ, Fin ν ⊢ F ≈ F' @ l → DVec^l(ν; F) ~ DVec^{l'}(ν'; F') @ l`.
The algorithm follows: `actne_dvec` compares levels, lengths by
`ac_tmnee`, and families by `ac_ty` under `i : Fin ν` (the left length).

## `dnth` (design point)

Doc §3, transcribed binder by binder (all of `n`, `F`, `cs`, `i` in `Γ`,
`F` under `i : Fin n`; `Emb_K := Π^{0,0}(Fin K). Fin n`):

```
dnth^l(n; F; cs; i) :=
  app (app (app (natrec^l (k̂. dMot) dBase dStep n) (λ^{0,0}(i : Fin n). i)) cs) i
dMot  (Γ, k̂)    := Π^{0,l}(e : Emb_k̂). Π^{l,l}(cs : DVec^l(k̂; j. F[e j/i])). Π^{0,l}(i' : Fin k̂). F[e i'/i]
dBase (Γ)       := λe cs i'. elim_Empty^{l,0}(x. F[e x/i]; i')
dStep (Γ, k̂, r) := λe cs i'. case^{0,0,l}(Unit^0; Fin k̂; z. F[e z/i];
                     _. fst cs;
                     j. r (λ^{0,0}(y : Fin k̂). e (inr^{0,0}(Unit^0; Fin k̂; y))) (snd cs) j;
                     i')
```

with every application annotated by the type of its function, and the
projections by `DVec^l(S k̂; …)`'s `Σ` reduct. Three conversions the
typing derivation crosses, all at D and M:
- `dBase`'s scrutinee `i' : Fin 0` meets `Empty^0` (`Fin`'s reduction),
  and `dStep`'s `i' : Fin (S k̂)` meets `Unit^0 + Fin k̂`;
- `fst cs : F[e (inl ⟨⟩)]`, where the `inl` arm's type is `F[e (inl x)]`
  for `x : Unit^0`: **Unit-η** (`x ≅ ⟨⟩`), which `nth` did not need
  (its motive is constant);
- the recursive call is at the family `F[(λy. e (inr y)) j]` and the
  outer application at `F[(λi. i) i]`: **β**, the step doc §3 flags.

`V_dnth` is `V_nth`'s composition with these three conversions added as
validity of type equalities (`F`'s validity at related indices, the
indices related by Unit-η's or β's validity). The design's question is
whether that composition goes through; the answer is M17a's.

Heather's neutral-tuple property (doc §3: `dnth(3; F; cs; inr (inl ⟨⟩))`
reduces to `fst (snd cs)` for a neutral `cs`) is checked as an untyped
reduction, as `nth_reds_*` (M15a).

## M17a outcome

Done, no admits or axioms. Files:
- `Validity/DVec.v`: `DVec` through the relation (`LR_dvec_nat` over
  `DFam`, as designed), validity (`V_dvec`, the computation rules), the
  generic law `gne_ty_dvec`, the algorithm (`actne_dvec`) and its
  soundness, completeness and decidability. The relation needed no new
  case, as planned.
- `Typing/DNth.v`: `dnth_wf`, the typing derivation of the schema
  above. Its Ltac (`gvar`'s context search) is at the top level, so
  `Validity/DVecNth.v` reuses it.
- `Validity/DVecNth.v`: `V_dnth`, `dnth`'s index lemma, composed along
  `dnth_wf` as `V_nth` is. The three conversions went through as
  designed:
  - the embedding `e` is carried as a valid term of `Emb_K` in an
    extended context, and its applications are related by one
    generalised lemma (`VG_emb_app_g`) whose right-hand annotation is
    free, so the identity embedding and the composed `λy. e (inr y)`
    are both instances;
  - β is `VG_fam_beta`: `F[(λy. b) s]` and `F[b[s]]` are related
    types, from `VG_beta` and `F`'s validity at related indices
    (`VG_fam_rel`);
  - Unit-η is `VG_unit_eta` at the `inl` arm (`VG_fin_inl`/`_inr` give
    the injections' validity at `Fin(S k)`'s reduct).
  `VTy_single`/`VTyG_single` moved from `ValidS.v` to `App.v`, so the
  file needs neither `ValidS` nor the substitution lemmas behind it.
- The neutral-tuple property is checked on doc §3's own instance
  (`Validity/DVecNthReds.v`, `dnth_reds_example`): `dnth(3; F; cs;
  inr (inl ⟨⟩))` reduces to `fst (snd cs)` for any `cs` in normal form,
  ten steps (two `natrec`s, the rest β and `case`). It is a leaf no
  file requires, so it costs the build CPU, not wall time.

## M17b: syntax and rules

De Bruijn layout, in `Γ`: `tyIWf l li X A N Ot C m` with the index type
`X @ li`, the shapes `A @ l`, the arity `N : Nat` and the output index
`Ot : X` under `x : A`, the child index `C : X` under `x : A, i : Fin N`,
and the index `m : X`; the type lives at `lmax l li`.
`tmSupi l li X A N Ot C a cs : IWf(…)(Ot[a])` with
`cs : DVec^{lmax l li}(N[a]; i. iwfFam … a)`, `iwfFam` the tree type at
the child index `C[a, i]`. `tmElimIWf l li l' X A N Ot C M c m t`: the
motive `M` binds `j : X, z : IWf(…)(j)`, the step `c` binds the shape,
the children and the induction hypothesis (`iwfcsty`, `iwfihty`,
`iwfstepty` in `Term.v`, as `Wf`'s), and the result is `M[m, t]`. β fires
at a `sup_i` of any annotations and any index (`red_elimIWf_supi`), to
`c[a, cs, iwfIH …]`, where `iwfIH` is `λ(k : Fin N[a]). elim_IWf(…)(C[a,
k])(dnth … cs k)`.

**Two admissible premises are stated** (a deviation in form, not in the
system). `dnth`'s typing (`Typing/DNth.v`) needs inversion, which comes
after presupposition, so presupposition cannot derive `dnth`'s typing,
and `Wf`'s route (`Wf_ih_eq`, `Wf_IH_wf` from `nth_wf`) is closed to
`IWf`. So `eqtm_elimIWf` states the induction hypothesis's types equal
(`iwfihty … ≅ iwfihty …'`), and `eqtm_elimIWf_supi` states `iwfIH`
typed at `iwfihty[a, cs]`. Both follow from the other premises once
`dnth_wf` is available, which is where every rule-building site (the
algorithm's soundness, subject reduction) is. The rules are gated by
`compt i`, as `DVec`'s.

## M17b: the relation for `IWf` (design)

MX §11's `Wf` relation with an index (doc §9). `LRiwf` keeps `Wf`'s
domain family `domR` and arity premise and adds the index type's
relation (`I` is a type at `li`, related in every world as `domR`), a
term relation at `I` for the output index `o` (in every world, related
shapes give related `o[a]`) and for the child index `c` (related shapes
and related `Fin` positions give related `c[a, i]`), and the index
`m ~ m'` at `I`. The term relation is `Wf`'s three mutual families with
the index as an *index* of the families, not a parameter, since each
child sits at its own index:

- `IWfRel m t t'`: both sides reduce, at the left `IWf(m)`, to whnfs
  related generically and by `IWfNf m`;
- `IWfNf m`: two `sup_i`s whose annotations agree with the type's, whose
  shapes are related in every world, whose output index `o[a]` is related
  to `m` at `I` (this is the whole of "the constructor is at its result
  index", read through conversion), and whose children are related in
  every world by the spine; or two neutrals;
- `DVecSp k k' (i. c[a, i]) cs cs'`: the relation at
  `DVec(k; i. IWf(c[a, i]))`, by cases on the lengths' reducts; at a
  successor the head is related by `IWfRel` at index `c[a, inl ⟨⟩]` and
  the tail by `DVecSp` at the moved family `c[a, inr j]`.

`elim_IWf` is valid by induction on the three families, with the motive
at index `j := m`: at a `sup_i` the step's type is at `o[a]`, related to
`m` by the `IWfNf` premise, and `M`'s validity at related indices turns
one into the other. The spine motive is `Wf`'s, through `dnth`.

## M17b outcome

Done, no admits or axioms (`Print Assumptions` of `wf_tm_dec`,
`preservation_tm` and `closed_canonicity` is empty). `IWf`, `sup_i`,
`elim_IWf` and β hold at layers D and M through the relation, validity,
the fundamental theorem, the algorithm, decidability, the type checker
and the consequences, as M15a's `Wf`. Files:
- `LogRel/Def.v`: `LRiwf` over `IWfRel`/`IWfNf`/`DVecISp`, as designed,
  and `PosRel` (below); `LogRel/IWfAux.v` the Kripke-world syntax, the
  rest of `LogRel` (escape, irrelevance, symmetry, transitivity,
  weakening, level invariance, permutations, neutrals) one case each.
- `Typing/PresupIWf.v` (presupposition's lemmas: the signature `IWfSig`,
  its equations `IWfEq`, the telescope), `Typing/IWfIH.v` (the
  synthesized induction hypothesis typed through `dnth_wf`).
- `Validity/IWf.v` (formation, `sup_i`), `Validity/IWfSp.v` (a `sup_i`'s
  spine to the relation at its `DVec`), `Validity/IWfElim.v`
  (`elim_IWf` and β), `Validity/DNthReds.v` (how `dnth` computes,
  untyped, at any state).
- `Validity/AlgDecIWf.v`: the decision cases, a part of its own.

Decisions and deviations, in the order the proof met them:
- **The annotations' agreement is declarative.** `IWfNf`'s `sup_i` case
  relates the node's annotations to the type's by `IWfEq`, declarative
  equations, not generic ones as `Wf`'s: symmetry moves them into the
  other side's contexts, and `C` lives two binders deep (`Γ, x : A,
  i : Fin N`), where the generic laws convert only the last entry. A
  generic law `geq_tm_ctxconv2` converts the second-to-last entry for
  the child index's other uses. `geq_tm_supi` takes the equations
  declaratively too; the algorithm compares only shapes and children
  (`actmnf_supi`, as `actmnf_supf`).
- **Positions are a relation of their own** (`PosRel`): the child index
  premise quantifies over related positions of `Fin N[a]`, and the
  relation at `Fin` cannot occur inside `LR`'s own definition. Neutral
  positions make the child indices generically equal at the position
  variable, which the spine's generic annotations need at a neutral
  length.
- **The motive is index-agnostic** (`IWfElim`'s header): the induction
  runs at the tree's own index, a `sup_i` sits at `Ot[a]`, and the
  eliminations are compared at the scrutinee's index, which `IWfNf`
  relates to `Ot[a]` (`LR_IWf_at`).
- **`dnth`'s states up to joinability.** The child the induction
  hypothesis reaches is a projection at the annotations `dnth`'s
  `natrec` step writes, not the spine's, so the spine's motive compares
  tuples and children up to reduction to a common term or to neutrals
  (`Join`, `TC` in `DNthReds`).
- **The two admissible premises are admissible in-tree.** `IWf_IH_wf`
  types β's induction hypothesis and `IWf_ihty_wf` types the `ih` entry's
  type from the motive (both through `dnth_wf`); the type checker builds
  the latter instead of deciding it. The congruence's equation of the
  induction hypotheses' types stays a premise. The algorithm's
  `actmne_elimIWf` had the matching premise (`ac_ty` at the two `ih`
  types) until 2026-10-20, when `IWf_ihty_eq` (`Validity/IWfIhEq.v`,
  ELIM_CONGRUENCE.md) derived the equation from the signatures' and the
  motives' at the computing layers.
- **Type validity of the rules' types.** `sup_i`'s type (the index
  `Ot[a]`) and `elim_IWf`'s (the motive at the scrutinee) have
  type-validity lemmas of their own (`V_supi_ty`, `V_elimIWf_ty`,
  `V_elimIWf_supi_ty`); their `VS_` wrappers take the scrutinee first,
  so that `s_lift` fixes the signature.
- **Build-graph moves.** The `gwa_` lemmas of `elim_IWf`, `dnth` and the
  induction hypothesis live in `GLift` (whose `gl_push` covers `IWf`),
  and `Fundamental` exports `Lam` last, so that `LogRel.Def`'s
  `gdecl_gwa` stays the one in scope downstream (`MetaV` broke on the
  other order).
- **Preservation at any index.** β fires at a `sup_i` of any annotations
  at any index `m`; `RS_elimIWf_supi` equates the `sup_i` with the
  canonical one at `m` (its output index is, by inversion) before the
  declarative β, which is stated at `Ot[a]`.

## M17c outcome

Done, no admits or axioms (`Print Assumptions` of `wf_tm_dec`,
`preservation_tm` and `closed_canonicity` is empty). The codes
`TmDVec`, `TmIWf` decode to `DVec^l(len; i. El fam)` and
`IWf(El x; …)(m)` (doc §6); `DVec`, `IWf`, `sup_i`, `elim_IWf` and the
codes are typed at every layer but V (the computing rules and β stay at
D and M), and the code recursor has the six branches `t_DVec`,
`t'_DVec`, `t_IWf`, `t'_IWf`, `t_supi`, `t_elimIWf` at 55–60
(`nbr = 61`). Staged in three commits, as M15b:
- **The codes at D and M first** (`compt i`, as the types), through
  decidability, canonicity, preservation and synthesis; then the lift to
  layer C: `StaticCode`/`PresupC` for the formers, `Typing/DNthG.v`
  (`dnth`'s typing at any layer, as M15b's `nth_wf_g`) and
  `Typing/IWfIHG.v` (the motive, the children's tuple and the induction
  hypothesis typed at any layer, from the signature alone), and the type
  checker (`TCType`, `TCSynth`) deciding them generically.
- **The branches through the early metatheory**: reducts
  (`Syntax/Recursor.v`), scopes (`RecSpec`) and the laws of renaming,
  substitution, global renaming and substitution, level equivalence and
  deep normal forms (`RecLaws`, `RecGSubst`, `GRenSyntax`, `SubstRec`,
  `LevelRed`, `TypedDnf`).
- **The branches through the relation**: `Validity/RecSIWf.v` (one lemma
  per branch, as `RecSWf`), wired into `RecS`'s `rec_code`; the typing of
  the reducts (`RecReductCases`, `RecAdm`).

Decisions and deviations, in the order the proof met them:
- **The scopes are derived, not transcribed.** Heather has no `rec.rs`
  branches for `IWf` yet, so the six scopes are stated from the layer-C
  rules (`RecSpec`, levels `ℓ ℓi ℓ'` bound in that order) and checked by
  `br_calls_derived`, as M15b's. They are the first precise statement of
  the branches; Heather's are to be checked against them.
  `t_elimIWf`'s calls exclude the step telescope's types, as
  `t_elimWf`'s do.
- **`elim_IWf`'s step scope is typed concretely** (`br60_scope`,
  WfScope) by `RecWf`'s automation, with a conversion prover (`weq`) for
  the β and Unit-η steps `dnth`'s unfolding crosses. The eliminator
  itself at C (`br60_head`, `Typing/WfScopeIWf.v`) is typed from
  `IWfIHG`'s generic lemmas, which the automation does not find on its
  own; `RecAdm` and `AlgPrereq` share it, so `RecAdm` now waits on
  `IWfIHG`.
- **Right payloads at the left levels.** A branch's right payloads are
  typed in the right context at the left levels and at the right
  payloads' instance (`GSone`): each is converted along the earlier
  calls' equations (`IWfEq_intro` packs them, at the right levels and at
  the left ones), then moved along the context equation.
- **Declared types under a binder.** The child index `X⟨↑⟩⟨↑⟩`, the
  output index under the shape and `sup_i`'s children's tuple
  `DVec(N[a]; i. iwfFam …)` carry weakenings and substitutions of
  payloads; `gs_norm` (RecSBase) and the branch tactics (`sr_ctx_IWf`,
  `res_eq_IWf`, `rr_ctx_I`, `rr_sh`) push the substitutions through
  them as equations before `cbn` (the gotcha in `docs/gotchas.md`, raw
  fixpoints). `AlgPrereq`'s branch automation gained globals under two
  binders (`wf_gv_up2`, `wf_gu_up2T`).

## `dnth`'s typing before weakening (2026-10-15)

`elim_IWf`'s branch scope (`wf_brG_60`) holds `dnth` in its induction
hypothesis's type. `RecWf`'s automation typed it by its unfolding (a
`natrec` with β and Unit-η conversions), 85 s on the critical path,
because `dnth_wf` (`DNth`) needs weakening, substitution and inversion,
which come after `RecWf`. Now:
- **`DNthCore`** holds the derivation, ported from `DNth`, with
  the family's instances as premises instead of metatheory: `n` under
  `m` locals (`NW`), `F` at an index under `m` locals (`FW`, `FV`) and
  at equal indices (`FE`, `FE0`). Each premise ranges over the numbers
  of locals the derivation uses (`2 <= m <= 9` for `FW` …), and an index
  is an application `e K x` or `var 0`, not any term, since a
  substitution holding an abstract term does not compute (`lcons'`
  inspects it) and the automation must normalize its instances. The two
  uses of inversion became direct derivations (`HEm`, `HRest`). It needs
  only `Declarative` and `SubstCommute`.
- **`DNth`** derives `dnth_wf` and its parts from `DNthCore`'s, the
  premises discharged by weakening and substitution (`extn_wkr`,
  `fam_wf`, `fam_eq`); its own copy of the derivation is gone, and its
  statements (used by `DNthG`, `DVecNth`, `IWfIH`) are unchanged.
- **`RecWf`** types `dnth` by `wf_dnth_eq` (the core at the expected
  type), each premise discharged under abstract locals by `dnth_ext`
  (one goal per number of locals, the abstract index typed by its
  hypothesis, `wty_hyp`). The automation and every other branch moved
  to `RecWfBase`, whose `wty` reaches the lemma through an `Ltac` hook
  (`wdnth`) that `RecWf` redefines (`::=`), so `RecWfBase` builds beside
  `DNthCore` and only `wf_brG_60` waits for it. `RecWf` keeps
  `wf_brG_60` and `wf_brG`; its users (and `WfScope`'s `br60_scope`,
  through the hook) are unchanged.

Clean builds at -j4, back to back on one 4-core machine: 1189 s →
1121 s wall, critical path 1047 s → 973 s, CPU 2826 s → 2762 s;
`wf_brG_60` 85 s → 24 s. `DNthCore` (61 s) is now on the path, but
`TypedDnf` then `RecWfBase` finish only 10 s before it, so splitting its
`dnth_step_wf` (50 s) by branch, `RecS`-style, would buy at most that.

## Two lemmas for Heather's no-UIP model (2026-10-17)

The independent review of Heather's `docs/no-uip-model.md` §4
(`docs/no-uip-model-review.md` there) suggested mechanizing two lemmas
its fixes rest on. Both are checked, with no admits or axioms:
- **`□`'s fibres are invariant under D-conversion**
  (`Typing/BoxFibre.v`, a leaf file). `box_fibre_ty_iff` takes
  `eqty_CTyp`'s premises (`Δ ≅ Δ'` at D, `l ≡ₗ l'`) and gives
  `[Δ ⊢[lC] T @ l] ↔ [Δ' ⊢[lC] T @ l']`; `box_fibre_tm_iff` takes
  `eqty_CTrm`'s (and `T ≅ T'` at D) and gives the same for C-terms. Both
  are corollaries of `ctxconv_ty`/`ctxconv_tm`, with `wf_conv` at C
  converting at `typeof lC = lD`. The model needs them to take `CΠ`/`TΠ`
  over conversion classes (its review's R2).
- **`unf` is idempotent** (`unf_idem`, `unf_idem_ty`, `unf_idem_ctx`,
  `unf_l_idem`, `unf_o_idem`, `Syntax/Unfold.v`), by one mutual
  induction: the `gdef` case is `unf_subst` with the induction hypothesis
  on the body, and the local substitutions are equal lookup-wise
  (`unf_l_canon`). The model stores box values unfolded (its R3).

## The generator's lowerings, in the formalization's rules (2026-10-20)

Heather's `docs/iwf-former-design.md` §13 step 6 (the generator) lowers
a surface family to one `IWf` (§8.1). `probes/IwfLowering.v` writes that
lowering in this syntax at layer D for the families §8.2 and §12 name,
and derives, with the M17b rules and nothing else, each family's typing,
its constructors' β through `elim_IWf` at an open index, and §8.3's
form A where it applies. `probes/IwfProbe.v` checks the same lowerings
in plain Coq; this one checks them against the rules. No family needed a
rule the frozen §1–§6 lack, so the task's abort criterion was not hit.
There are no admits or axioms (`Print Assumptions` at the end of the
file).

| family | index | checked |
|---|---|---|
| `Vec a` | `Nat` | typing; `vhead (vcons n y xs) ≡ y` by form A; `len (vcons …) ≡ S (len xs)`, the child through `dnth` |
| F3 `Cons(n, x : Fin n, xs)` | `Nat` | typing; `head (cons n x xs) ≡ x : Fin n` by form A, the result type depending on the index |
| F1 `Node(l : T 0, r : T n) : T (S n)` | `Nat` | typing; `left (node n l r) ≡ l : T 0` by form A |
| F2 `Node(n, l r : T n) : T (n + n)` | `Nat` | typing; β at the stuck index `n + n` (`size (node n l r) ≡ S (size r)`) |
| `All p : List a → Type` (§12.1) | `List a` (tier 0's `Wf`) | typing; `allHead (allCons xs x px rest) ≡ px` by form A |
| `Even`/`Odd` (§12.2) | `Σ(b : Bool). Nat` | typing; `toNat (esucc n o) ≡ S (toNat o)`, the child at the other tag; `Odd 0 → Empty` by form A |

Negative controls: a constructor at an index other than its output
index has no derivation (`nil3_not_at_one`, `leaf1_not_at_one`,
`node1_not_at_zero`), nor one at the other family's tag
(`ezero_not_odd`). `inv_supi` and `decl_IWf_inj` give the indices'
conversion, a large elimination into `⌜Unit⌝`/`⌜Empty⌝` turns it into
`Unit ≅ Empty`, and `decl_head` refutes that.

Findings, for the generator (Heather's §8.1, §8.3, §12.1, §12.2):
- **The child index and the step carry the position through the tag's
  case (a convoy).** §8.1's "case on the tag, then on the literal
  position" does not typecheck as written: the position `i : Fin N[x]`
  has a type that mentions the tag, and a case on `x` does not refine
  `i`'s type. So the case on the tag returns `Π(i : Fin N[z]). I` and is
  applied to `i` (F1's `c`). A step that uses the children or the
  induction hypothesis at a literal position does the same, with
  `Π(cs : DVec N[z] …)` or `Π(ih : Π(i : Fin N[z]). M …)` (`len`, F1's
  `left`, F2's `size`, `toNat`). A child index that ignores the position
  (Vec, F2, F3, All, Even/Odd) needs no convoy, and neither does a form A
  arm that reads only the payload (`vhead`, F3's `head`, `allHead`).
- **Form A needs only `I`'s own eliminator, into `Ty 0`.** The motive
  cases on the index by `natrec` (Vec, F1, F3), by `elim_Wf` (§12.1: at
  `List a`, tier 0's lowering, nothing more is needed), or by the
  projections and then `Bool`'s case and `natrec` (§12.2, at the Σ
  index; no Σ-η, since the output indices are literal pairs). The arms
  are codes: `⌜Unit⌝` at the impossible indices, and at the possible ones
  the result type's code (`a`, `⌜Fin k⌝`, `p y`, `⌜Empty⌝`). So the one
  requirement beyond `I`'s eliminator is on the *result*: it must have a
  code. When the result is a value of the family itself (F1's `left`,
  `T 0`), the arm is the family's own code `tmIWf(⌜I⌝; ⌜S⌝; n; o; c; 0)`,
  so `I` and the shapes must have codes too. For `Nat` they do; at
  `List a` they do (`a` is a code and `List` decodes from `tmWf`), and the
  inversion to `All p xs` is checked below (2026-10-21).
- **§12.2 needs nothing new** for families over a common `I_tag`: one
  shape summand per constructor of either family, indices pairing a tag
  with a number, and mutual recursion as one `elim_IWf`. A tag-dependent
  `I_tag` (`Σ(b). I_b` with `I_b` varying) would need the motive's case
  on `snd j` at a type depending on `fst j`, a convoy again. Checked
  below (2026-10-21).
- F2 at `n + n` is tier 2 (index abstraction), the elaborator's, so not
  checked here; β at the stuck index is.

The checker (`pty`, `ptm`, `pconv`, `ptmconv`) is syntax directed over
`Declarative`'s rules, with conversions through weak-head normal forms
by `Preservation`'s soundness of reduction and `elim_IWf` typed from
`IWfIH`'s lemmas. Three things kept it usable:
- Substitutions are normalized by `lazy`, not `cbn` (`cbn`'s refolding
  made `dnth`'s reduction steps take minutes; `lazy` takes 0.1 s).
- The induction hypothesis stays folded (`iwfIH`), typed by
  `IWf_IH_wf`, never through `dnth`'s unfolding. The cost: the checker
  cannot normalize a step whose body passes the hypothesis under a
  binder, since `lcons'` inspects the substituted term (as `DNthCore`'s
  note says for abstract terms). F2's `size` therefore counts the right spine only;
  `size l + size r` through `natrec` would need a commutation lemma for
  `iwfIH`.
- Each family's type and conversion at any index are lemmas proved once
  (`F1T_wf`, `AllT_conv_4`, …) and reached through `Ltac` hooks
  (`pfam_ty`, `pfam_conv`), as `RecWfBase`'s `wdnth`; `All`'s are per
  depth, over any context whose entries at `d`, `S d` are `p`, `a`.
  Without them `allCons` took 12 minutes and the file ran out of memory.
The file is not in the build; it compiles in about 25 minutes and 6 GB of
memory (34 minutes on the 4-core cloud machine of 2026-10-21).

## The two cases left unchecked (2026-10-21)

The checker moved to `probes/IwfCheck.v` (its Ltac at the top level, so
that other files can use it; `IwfLowering.v` is otherwise unchanged and
recompiles closed), and the two cases above are checked in two more
probe files, with the same method: the M17b rules only, the induction
hypothesis folded, each family's pieces proved once behind the hooks,
negative controls, `Print Assumptions` closed. No case needed a rule
the frozen §1–§6 lack, so the abort criterion was not hit.

| file | family | index | checked |
|---|---|---|---|
| `IwfLowering2.v` | `A : Nat → Type`, `B : Bool → Type`: `anil : A 0`, `acons(n, y : Nat, h : B true) : A (S n)`, `bleaf : B false`, `bnode(n, c : A n) : B true` | `Σ(b : Bool). El(case b of ⌜Nat⌝ \| ⌜Bool⌝)` | typing; β across the tags both ways (`size_acons`, `size_bnode`); form A at both tags (`apay_beta : pay (acons n y h) ≡ y`, `bpay_beta : pay (bnode n c) ≡ n`); `bleaf` not at `B true`, `anil` not in `B` |
| `IwfLowering3.v` | `All p` of `IwfLowering.v` | `List a` | the codes `⌜List a⌝`, the shapes', `⌜All p m⌝` (`allC_ty`), `El ⌜All p m⌝ ≅ All p m` (`allC_el`); `allTail : All p (x :: xs) → All p xs` by form A, typing and β at an open `allCons` (`allTail_beta`) |

Findings, for the generator (Heather's §8.1, §8.3, §12.1, §12.2):
- **A tag-dependent index type is a Σ over a large elimination.** With
  `I_b` varying, the index type is `Σ(b : Bool). El(I(b))`, where `I` is
  the tag's case into `Ty 0` with each `I_b`'s code as an arm. So the
  `I_tag` must have codes, the same requirement form A puts on its
  result. A literal pair `(tag, v)` types through the case's β (`v : Nat`
  against `El(I(inl ⟨⟩))`), so the output and child indices need no
  annotation beyond the pair's.
- **The motive's case on `snd j` is a convoy on `fst j`.** `snd j` has
  type `El(I(fst j))`, which a case on `fst j` does not refine. So the
  case on the tag returns `Π(v : El(I(z))). Ty 0`, each arm a `λ` that
  eliminates its own `I_b` (`natrec` at `Nat`, `Bool`'s case), and is
  applied to `snd j`. The negative control separating two indices with
  the same tag is the same convoy (`Dv`). The step needed nothing new:
  `pay` reads only payloads, and `size` carries the induction hypothesis
  through both levels of its case on the shape (tag, then constructor),
  the inner case's motive being the outer one's at `inl`/`inr` of its
  own variable.
- **Form A into the family itself at `List a` needs a convoy in the
  motive too.** The motive at index `j` is `El(elim_Wf(j; …))`, whose
  `cons` arm returns `⌜All p (tail)⌝`. The tail is the index's child, in
  `cs : Vec(N[b]; List)`, whose type mentions the shape, so `List`'s
  case on the shape returns `Π(cs : Vec(N[z]; List)). Ty` and is applied
  to `cs`. In general: the motive's index elimination carries whatever
  of the index's own data (children, or a dependent component) the
  result type reads.
- **The codes exist and decode up to the components' `El`.**
  `⌜All p m⌝ := tmIWf(⌜List a⌝; ⌜Unit⌝ + Σ(xs : ⌜List a⌝). Σ(x : a). p x;
  n; o; c; m)` with `⌜List a⌝ := tmWf(⌜Unit⌝ + a; n)`, all typed from
  `a` and `p x` being codes. `El ⌜All p m⌝` reduces to `IWf(El ⌜List a⌝;
  El ⌜S⌝; …)(m)`, which converts with `All p m` component by component
  (`El` of `tmWf`, `tmSum`, `tmSig`), not syntactically; the arity,
  output and child index are shared. The motive lands in `Ty (0 ⊔ 0)`,
  `IWf`'s level, so the codes are at `U (0 ⊔ 0)` and the motive's
  `elim_Wf` at its successor.

The checker's costs, for the record (they are this probe's, not the
kernel's): `IwfLowering2.v` takes about 13 minutes and `IwfLowering3.v`
about 63 minutes and under 13 GB of memory, on one 4-core cloud machine.
Two devices kept them feasible, as the hooks did for `IwfLowering.v`:
- each step is typed once in its telescope (`sizeStep_wf`, `payStep_wf`,
  `tailStep_wf_4`) and reached through a hook that normalizes the
  lemma's statement as `pn` normalizes goals, keyed on the step's head;
  without it every β retyped its step, and `apay_beta` and `allTail_wf`
  ran out of memory;
- the signature's components are proved once in the context the
  signature binds (`abO_wf` over `Γ, x : S`), not at an abstract shape:
  a substitution of an abstract term does not compute (`lcons'`), so
  the abstract version did not normalize.
`allTail_wf` is stated at `allTail_beta`'s depth (one unused variable)
so that one step lemma serves both; the step's typing is about a
quarter of the file's time.
