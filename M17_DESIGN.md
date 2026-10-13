# M17: indexed finitary trees (`DVec`, `IWf`), design

Status: **M17a done** (2026-10-13); M17b next. Why now: Heather froze `IWf`'s
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

## M17b: the relation for `IWf` (design, ahead)

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

## M17c: codes and branches (design, ahead)

`TmDVec { l, len, fam ⟨i⟩ }` decoding to `DVec^l(len; i. El fam)` and
`TmIWf` decoding to `IWf(El idx; …)(at)` (doc §6), and the branches
`t_DVec`, `t'_DVec`, `t_IWf`, `t'_IWf`, `t_supi`, `t_elimIWf` at
55–60 (`nbr = 61`), their scopes derived from the layer-C typing rules
as M15b derived `Wf`'s, with `br_calls` checked against
`br_calls_derived`.
