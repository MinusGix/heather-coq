# Milestone 4: universe polymorphism (`UΠ`, `Λ`, `$`) and ω

Goal: extend M3 with universe-polymorphic functions. That means the type
`UΠ ℓ⃗. T` at level ω, the abstraction `Λ ℓ⃗. t` and the application
`t $ l⃗`, with their β and η rules, the relation at ω, and the fundamental
theorem at M with the new rules.

Paper references: 04:83–95, 04:128–180 (syntax, ω), 04:560–576 (formation),
04:626–632 (type congruence), 04:686–694 and 04:749–757 (typing and
congruence), 04:1455–1463 (β, η), 05:21, 05:119, 05:223 (the operations),
06:21–31 and 06:75 (whnf, reduction), 06:510–515 and 06:584–587
(algorithmic conversion), 07:296–342 (generic laws), 07:432–440 (ω needs
a transfinite stage), 07a:848–890 (the relation at ω), 07b:1640–1700 (the
semantic rules), 08:38 (injectivity).

## Scope

| Stage | Contents |
|---|---|
| **M4** (this doc) | `UΠ`/`Λ`/`$` (syntax, operations, typing, metatheory), the relation at ω, the semantic rules, the FT at M, consequences at ω |
| M2b | `CΠ`, `TΠ` (unchanged plan; independent of M4) |

## Observations that shape the design

- **ω only occurs as the level of a judgment.** ω is not well-formed
  (`lwf _ lomega = False`, 04:245). Every premise that places a type in a
  context, a Π, a universe, a global declaration or a motive requires
  `lwf`. So the only judgments at ω come from the new rules and from the
  generic ones: refl, sym, trans, type conversion and `≡ₗ`. The level
  conversion rules need `lequiv`, which excludes ω, so they never fire
  at ω.
- **Types at ω are `UΠ` up to conversion, and nothing at ω is neutral.**
  Every elimination form has its type at a well-formed level (`$`
  included: `l[l⃗/ℓ⃗]`), and variables of either kind have well-formed
  levels. The paper's neutral law for `$` (07:340) is still stated, for
  the generic interface, but the relation at ω needs no neutral case.
- **`UΠ` never occurs inside another type's relation.** Nothing at ω can
  be a Π domain or codomain, a universe element or a code, so the relation
  at ω refers to the finite relation but never the reverse. In the paper
  this is the single "large cardinal" of the transfinite recursion
  (07:435).
- **M3 already has the universe binders.** The level lists (`uext ls φ`),
  the iterated lifts (`uupn`, `uuprn`, `uwkn`, `guwkn`), universe weakening
  of global contexts (`gctx_uwk n G`), worlds with level growth, and
  permutations (E14: `LR_uwk`) are all in place. The generic laws are
  also stable under universe substitution.

## Decisions

### F1. Syntax: one n-ary level binder, annotations as in the paper

- New `ty`: `tyUPi (n : nat) (l : lvl) (T : ty)`, where `T` and `l` bind
  `n` levels.
- New `tm`: `ulam (n : nat) (l : lvl) (t : tm)`, where `t` binds `n`
  (superseded in M7 C1b: `ulam n l T t`, annotated with its body type)
  levels, and `uapp (t : tm) (ls : list lvl)`.
- n-ary, as in the paper. A unary `UΠ` cannot be nested: the body of
  `UΠ` must be at a finite level, and `UΠ` lives at ω. `n > 0` is a typing
  premise, not a syntactic constraint.
- De Bruijn order follows `uext`: `ls` lists the levels in binding order,
  so its last element instantiates `lvar 0`. Instantiation is
  `T[uext ls lvar]ᵤ`.
- Operations under the binder: universe renaming and substitution use
  `uuprn n`/`uupn n`, local substitution `uwkn n`, global substitution
  `guwkn n`, and local and global renamings pass unchanged. No new scope
  markers are needed (E2's markers exist for the recursor bundle), and
  the iterated single-step lemmas from M3 discharge the new cases.
- `$` carries no type annotation, following the paper. Annotations exist
  on `app` for the code recursors, and `UΠ`/`Λ`/`$` are not code (M only),
  so no recursor ever inspects them.

### F2. Typing: M-only rules; judgments at ω reuse the existing sorts

The level `lomega` is a judgment level like any other, so the four mutual
sorts stay unchanged, and so do the `*_all` statements (as in M3 E2).
Eight rules, all at layer `lM`. They follow 04 with the extended scope
`G⁺ := gctx_uwk n G`, `Γ⁺ := Γ` universe-weakened by `n`:

- `wft_upi`: `⊢ Γ`, `[G⁺; Γ⁺ ⊢ T @ l]`, `lwf (n + gL G) l`, `n > 0` ⇒
  `[G; Γ ⊢ tyUPi n l T @ lomega]`.
- `eqty_upi`: the congruence, with `lequiv (n + gL G) l l'` (04:626).
- `wf_ulam`, `eqtm_ulam`: body typed/equal at `G⁺; Γ⁺`.
- `wf_uapp`, `eqtm_uapp`: `t : tyUPi n l T @ lomega`,
  `[G⁺; Γ⁺ ⊢ T @ l]`, `length ls = n`, each level well-formed in
  `gL G` (pointwise `lequiv` for the congruence). The result is
  `T[uext ls lvar] @ l[uext ls lvar]`.
- `eqtm_ubeta`: `(ulam n l t) $ ls ≅ t[uext ls lvar]`.
- `eqtm_ueta`: `ulam n l (uapp t⟨ush n⟩ᵤ ℓ⃗) ≅ t`, where `ℓ⃗` are the
  bound variables.

Metatheory: every typing lemma gains these cases (weakening, global
weakening, local/global/universe substitution, context conversion,
presupposition, static code, typed deep normal forms, typed reduction,
lifting, functionality). The M-only gate makes the C and P layers
(`static_code`, `FundamentalS`) vacuous on the new rules.

### F3. The relation at ω: a top tier over the finite relation

The relation at ω is **not** a new constructor of `LR`. It is one
definition on top of `LogRel`:

```
UPiRel G Γ n l l' T1 T1' instR : tm -> tm -> Prop :=
  t, t' reduce to whnfs w, w' at the UΠ types, w ≈ w' at both, and
  ∀ ρ : kwk G Γ, ∀ ls ls' (length n, pointwise lequiv in gL (kw_G ρ)),
    instR ρ ls ls' (uapp (ktm ρ w) ls) (uapp (ktm ρ w') ls')

LRω G Γ T T' R :=
  T ⤳* tyUPi n l T1 @ ω, T' ⤳* tyUPi n l' T1' @ ω, n > 0,
  lequiv (n + gL G) l l',
  UΠ ≈ UΠ' @ ω, and
  ∀ ρ ls ls', LogRel l[ls] (kw_G ρ) (kw_Δ ρ)
                (kty ρ T1)[ls] (kty ρ T1')[ls'] l[ls] (instR ρ ls ls'),
  releq R (UPiRel … instR)
```

The instance levels `l[uext ls lvar]` are finite but unbounded. They are
handled by `LogRel` at each of them, so no stage index is needed at ω.

Why not a constructor. Every `LR` induction (irrelevance, symmetry,
transitivity, weakening, escape, reduction, level invariance,
permutations, layering) is a strong induction on the `nat` stage, with
`rec = LRbelow n`. An ω constructor would need a stage above every `nat`
and a different `rec`, so every one of those proofs would be
restructured. The top tier leaves them untouched. Each property at ω is
one direct lemma from the finite one, and in Π's terms the content is the
same as a new case would have. The paper's "transfinite recursion"
(07:435) is exactly this two-tier shape.

The paper's world `ψ` includes a universe weakening `θ`. Ours is `kwk`,
whose `gwk_ok` already allows level growth (E14). The level lists `ls`
are well-formed in the world's `gL`. Local and global renamings leave
level binders alone, so `kty ρ` acts on `T1` unchanged.

**Validity dispatch.** `LRty`/`LRtm`/`VTy`/`VTm` stay finite, and every
existing file keeps them. The ω tier has its own forms (`LRtyω`,
`LRtmω`, `VTyω`/`VTmω`, `VTyGω`/`VTmGω`, `VTySω`/`VTmSω`; OmegaV.v), not
a `match` on the level. The FT at M has a two-part motive for every
judgment at `l`:
`(lwf (gL G) l -> … finite …) /\ (l = lomega -> … at ω …)`. Each
induction hypothesis is used at its half: the finite half when its level
is well formed, the ω half when it is ω. For a rule concluding at a
well-formed level, the ω half is absurd (`w_absurd`). For a `UΠ` rule,
the finite half is absurd. The level dichotomy `judg_lvl` (UInst.v) says
every judgment's level is well formed, or ω at layer M.

(Implemented: `LRω` has no well-formedness premise for `T1`, `T1'` at
`G⁺; Γ⁺`. The semantic rules never needed it.)

### F4. Escape at ω: fresh levels at the top, then the rotation

Generic laws (07:296–342) added to `GenericEqLaws`:
- `geq_ty_upi`: congruence of `UΠ`.
- `geq_tm_uext`: extensionality. If `t, t' : UΠ` and
  `uapp t⟨ush n⟩ᵤ ℓ⃗ ≈ uapp t'⟨ush n⟩ᵤ ℓ⃗ : T @ l` at `G⁺; Γ⁺`, then
  `t ≈ t' : UΠ @ ω`.
- `gne_tm_uapp`: the neutral congruence.

The declarative instance proves extensionality by η.

Escape from `LRω` is direct (implemented): `LRupi` carries
`UΠ ≈ UΠ' @ ω`, and `UPiRel` carries `w ≈ w'` at both types. The
semantic rules establish both at the validity level, where the body's
validity is quantified over universe substitutions: `geq_ty_upi` and
`geq_tm_uext` get their `G⁺; Γ⁺` premises there (UPiV.v).

The growth-and-rotation argument is used for **injectivity of `UΠ`**
instead (DeclConsequences.v, `declM_upi_body`). Take the instance at the
world that grows `G` by `n` levels (`kw_grown`), with `ls` = the new
top variables (`utop`). The instance `T1[uext ls lvar]` is `T1` under the
rotation of M3 E14: bound variables go to the top, and the others move
down by `n`. Escape gives its conversion at the grown context. The
universe substitution along `rotn` is the inverse rotation, and it moves
the conversion back to `gctx_uwk n G; Γ⟨ush n⟩ᵤ`. The rotation acts on
the declarative judgments only; the relation at ω itself is never
permuted.

Properties of `LRω`, one lemma each from the finite relation and
determinism of whnf:
- irrelevance;
- symmetry and transitivity;
- stability under `kwk` (worlds compose);
- anti-reduction;
- escape.

Neutral reflection at ω is not needed (no neutrals at ω).

### F5. Semantic rules and the FT at M (07b:1640–1700)

- **Formation and congruence of `UΠ`:** the instance at `ρ`, `ls` is the
  body's validity at the universe substitution `uext ls φ` (validity is
  already quantified over `φ`, M3). The syntactic commutation is
  `T[uupn n φ]⦃guwkn n σ⦄[uwkn n δ][uext ls lvar] = T[uext ls φ]⦃σ⦄[δ]`
  (RecPeel has the `uext` laws).
- **`Λ` and its congruence:** likewise. The whnf equality comes from
  escape of the instances, via `geq_tm_uext`.
- **`$` and its congruence:** instantiate `LRω` at the identity world
  with `ls[φ]`.
- **β:** anti-reduction to the body's instance.
- **η:** at every instance, `(Λ ℓ⃗. t⟨ush n⟩ᵤ $ ℓ⃗) $ ls` β-reduces to
  `t $ ls`, which the validity of `t` relates.
- **Generic rules at ω** (refl/sym/trans/conv/`≡ₗ`): the `LRω` lemmas of
  F4.

### F6. Consequences

At ω, the M consequences are:
- weak-head normalization (every term at a `UΠ` type reduces to a `Λ`);
- injectivity of `UΠ` (08:38);
- discrimination of `UΠ` against the other type formers.

The existing consequences keep their statements. The generic lemmas
(Consequences.v) take the relation at well-formed levels only
(`red_eqty : … -> lwf (gL G) l -> LRty …`), and gain an `lwf` premise.
The declarative wrappers discharge it:
- at P, by `judg_lvl` (ω is at M only);
- at M, by `judg_lvl` plus the relation at ω. A whnf type other than a
  `UΠ` is never at ω (`lwfM_whnf_l`).

Normalization at M covers ω as well: types reduce to a `UΠ`, and terms
reduce to a whnf by `UPiRel`.

## Order of work

1. Syntax (F1): constructors, all operations, the `*_all` laws, `≡ₗ`,
   deep normal forms, scoping (`ty_lwf` under `n` binders), whnf and
   neutral forms, untyped reduction (`ulam` β, `uapp` congruence).
2. Typing (F2): the eight rules and every metatheory lemma.
3. Generic laws (F4) and the declarative instance.
4. The ω tier (F3): `UPiRel`, `LRω`, its properties, the `W` wrappers.
5. Semantic rules and the FT at M (F5).
6. Consequences (F6), README, agent notes.

## Gotchas known up front

- `leval _ lomega = 0`, so `leqv lomega lzero` holds. `≡ₗ` only compares
  levels inside typed syntax, which are well-formed. Never compare a
  judgment level by `leqv`.
- The paper's term relation at ω (07a:873–884) writes `w $ l⃗'` on both
  sides. The second `w` should be `w'`.
- The paper's type relation at ω takes the same `l` in both `UΠ`s. We
  allow `l ≡ l'`, as `LRpi` does for its annotations.

## Status

**M4 complete (2026-09-25).** No admits and no axioms: the consequences
are closed under the global context.
- Steps 1–2 (syntax, typing, metatheory): see History.
- Steps 3–4: the generic laws (Generic.v, DeclInstance.v), the relation
  at ω (LogRel/Omega.v) with its properties, and validity at ω
  (Validity/OmegaV.v).
- Step 5: the semantic rules (Validity/UPiV.v: `VS_upi`, `VS_ulam`,
  `VS_uapp`, `VS_ueta`, `VS_red`), and the FT at M with the two-part
  motive (FundamentalM.v, F3 above).
  - The recursors' β rules are absurd at ω via `elimT_lvl_wf` /
    `elimt_lvl_wf` (RecPeel.v).
  - `fundamentalM` states both halves. `Reducible` adds
    `reducibleM_eqty_ω` / `reducibleM_eqtm_ω`.
- Step 6 (DeclConsequences.v):
  - normalization at ω;
  - `declM_upi_inj`: arity, level equivalence and bodies (08:38);
  - discrimination of `UΠ` against ℕ, U, Π, `CTyp` and `CTrm`;
  - `upi_lvl`: `UΠ` types live at ω only.

### History

**Steps 1–2 done (2026-09-25).** Syntax, operations, laws, reduction,
the eight rules and the whole typing metatheory. Choices made on the way:
- The n-ary binder's operations are `Nat.iter` of the single-step lifts
  (`uuprn`, `uupn`, `uwkn`, `guwkn`, now in Syntax). Each single-step
  hint lemma has an iterated twin, proved by induction on `n`.
- Untyped β for `$` checks the arity (`length ls = n`). Without the
  check, β does not commute with universe substitution.
- The rules carry the body type's well-formedness (`T @ l` in the
  extended scope) wherever the metatheory needs it before substitution,
  as for the recursors (M3 E10).
- `Typing/UInst.v` holds the instantiation lemmas (a judgment in the
  extended scope, instantiated at `n` well-formed levels, holds in the
  original scope), the facts for η's bound variables (`ubvars`), and
  the presuppositions of the new rules.

(The temporary admit of step 2 in `fundamentalM_us` was removed in
step 5.)
