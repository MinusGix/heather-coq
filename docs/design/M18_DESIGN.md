# M18: Heather's indexed coinductive former (`M`, `corec`, `out`), design

Status: **M18a done** (2026-10-21): the rules checked against the
relation's shape and against a model, with two probes, before any change
to the theories. **M18b done** (2026-10-26): the former in-tree at
layers D and M, every kernel rule as Heather has it (outcome below).
**M18c** (codes) is planned below. Why now: Heather's kernel has the
former already (MinusGix/heather#111, merged 2026-10-21), implemented and
tested ahead of this repo's check, and its design asks three questions
here (`H/docs/kernel-coinduction-design.md` §9, "the design" below).

Heather's rules (the design §1–§2; `H/crates/kernel/src/term.rs`, the
`MSig` section, has the schemas that typing, both reducers and conversion
share; `H/crates/kernel/tests/m.rs` pins the verdicts):
- **Formation.** `M^{l,l',li}(I; i. S; i s. P; i s p. o)(j) @ l ⊔ l' ⊔ li`,
  for `I @ li`, `S @ l` under `i : I`, `P @ l'` under `i, s`, `o : I`
  under `i, s, p`, and `j : I`. Shapes depend on the index, the child's
  index is computed, nothing is stored.
- **Elimination.** `out(σ; j; m) : Σ(s : S[j]). Π(p : P[j, s]). M(σ)(o[j, s, p])`,
  the only eliminator, neutral on a neutral `m`.
- **Introduction.** `corec^{k}(σ; i. X; i x. c; j; x) : M(σ)(j)` with
  `X @ k` under `i : I` at any `k`, the step
  `c : Σ(s : S). Π(p : P). X[o] +^{k,f} M(o)` under `i, x : X`, and
  `x : X[j]`: the apomorphism.
- **β.** `out(corec(…; j; x)) ⇝ pair(fst r, λp. case(snd r p; y. corec(…;
  o[j, fst r, p]; y); t. t))` with `r := c[j, x]`, only under `out`.
- **Conversion.** No η. `M` types structurally; two `corec`s by carrier
  level, carrier, step (at the left step type), seed, the signature and
  index read off the type; a `corec` against anything else is not
  convertible; two `out`s by their scrutinees only.
- **Layers.** P and M only (here: D and M, `compt i`).

## Verdict

No kernel rule is wrong. Each of Q1–Q3 has a yes, with one refinement of
the proposed relation and one correction to the design text (not to the
kernel):

1. **Q1, the relation.** The ω-intersection works and keeps `M` a
   per-former case, with no carrier in it, **provided every depth keeps
   the clause of generic equality** (both sides reduce to whnfs related by
   `≈`, `WRel`'s first clauses). The observations alone are coarser than
   the kernel's conversion: they relate two `corec`s that conversion
   separates, and escape, hence completeness, would fail. The design's
   text has the clause ("the whnfs are declaratively equal"), but it
   should read "generically", since the algorithmic instance needs it.
   **The family level must contain `li`**, as `IWf`'s does, because the
   relation is stratified by level (below).
2. **Q2, decidability.** The algorithm fits the generic equivalence as an
   instance: the `corec` arm and the `out` arm are exactly the two generic
   laws the relation's proofs use (`geq_corec`, the neutral law of `out`'s
   projections), and the forced annotations are forced as
   `ELIM_CONGRUENCE.md` describes, through `M`'s injectivity. β is sound
   at an open, computed child index with no index conversion at all: the
   reduct's child sits at `o[j, fst r, p]`, which is the index `out`'s
   type asks for at the shape `fst r`.
3. **Q3, the bridge.** `Bisim t u ⇔ Π n. Same(approx n t, approx n u)` is
   checked. Left to right needs nothing. Right to left is a `corec` into
   `Bisim` and needs UIP on the shapes, which holds when they have
   decidable equality (Hedberg).

The correction, for Heather's design §1.4: the constructor
`in(σ; j; s; f) := corec(_. Unit; _ _. pair(s, λp. inr(f p)); j; ⟨⟩)`
types only when `I` is `Unit`. Its step is checked under the bound index
`i`, where `s : S[j]` is not an `S[i]` and `f p : M(o[j, s, p])` is not an
`M(o[i, s, p])`. At an indexed `M` (every coinductive predicate) the
constructor takes `out`'s type itself as its carrier:

```
in(σ; j; s; f) := corec^{f}(σ; i. Σ(s : S[i]). Π(p : P[i, s]). M(o[i, s, p]);
                            i x. pair(fst x, λp. inr(snd x p)); j; pair(s, f))
out(in(σ; j; s; f)) ⇝ pair(s, λp. case(inr(f p); …; t. t)) ⇝ pair(s, λp. f p) ≡η pair(s, f)
```

with the carrier at the family level `f`. The kernel's tests use the
unindexed form only (`Stream`'s `cons`), so they are right as they stand;
the elaborator's `codata` constructors (design §6) must use this one.

## M18a: the probes

Both are standalone (`coqc probes/<file>`, a few seconds each), closed
under the global context. Neither needs the theories: the first models
the rules in Rocq, the second checks the relation's arguments over an
abstract interface. Each was kept to what a full in-tree round would
otherwise answer only after weeks of work.

### `probes/MCoind.v`: the rules in a model, and the bridge

The former as a negative coinductive record with primitive projections
(`CoInductive M j := mkM { out : {s : S j & ∀ p, M (o j s p)} }`), whose
`cofix` unfolds only under a projection and which has no η: Rocq's form of
the same discipline. `corec` is a `cofix` with the kernel's step type.

- `out_corec`: β as `m_out_corec` writes it, by `eq_refl`, at an open
  index, carrier, step and seed. Rocq's type checker accepts the reduct
  at `out`'s type at `j`, with the `case`'s motive at the computed child
  index `o j (projT1 r) p`.
- `in_`/`out_in`: the indexed constructor above, `out (in_ j s f) =
  existT s f` by `eq_refl` (Π-η only). `in_unit_fails`: the design's
  `Unit`-carrier form at an indexed `M`, refused with "`s` has type `S j`
  while it is expected to have type `S i`". `in_unit`/`out_in_unit`: the
  same form at `I := Unit` types and computes.
- Negative controls, each a `Goal` whose `reflexivity` fails, mirroring
  `m.rs`: no η (`t = mkM (out t)`); two `corec`s of one stream, over the
  carriers `unit` and `nat`, are distinct (`zeros_u = zeros_n`); a tree is
  not its reconstruction `in (out t)`; a `corec` that rebuilds a variable
  is not the variable.
- `zeros_same`: the two distinct `zeros` have the same approximation at
  every depth, and `zeros_bisim` makes them bisimilar through the bridge.
  This is the counterexample of Q1: observations do not see carriers.
- `Bisim` (the design §4) as an instance of the indexed `M`: index the
  pair of trees, shape `shape t = shape u`, positions the left root's,
  the right child at the position moved by `eq_rect`. `bisim_refl` is a
  proof by coinduction, a `corec` whose carrier is the relation (here
  `fst ix = snd ix`).
- `IBisim`, the indexed variant: at an indexed `M` the two children sit at
  `o j s p` and `o j s' (e ▸ p)`, so the index is `Σ(j). M j × M j` and
  the right child is moved to the left child's index along the shapes'
  equation (`ikid_moved`, a `J` on `e`). `ibisim_refl` checks it. The
  design writes §4 unindexed; the indexed form needs this one transport
  more and nothing else.
- The bridge: `bisim_approx` (left to right, induction on `n`, no
  assumption) and `approx_bisim` (right to left, a `corec` with carrier
  `Approx (t, u) := ∀ n, Same (approx n t) (approx n u)`). The step takes
  the shapes' equation from depth 1 and, at depth `n + 1`, moves the
  child's sameness from that depth's equation to depth 1's by `UIP_S`.
  `approx_bisim_dec` discharges `UIP_S` by `UIP_dec`. This is
  `probes/ItreeDepthBisim.v`'s `UIP_Cmd`, now for the general indexed
  former's encoding rather than a hand-written `CoInductive`.

### `probes/MRelProbe.v`: the relation at `M`

The terms, the Kripke worlds (a preorder; weakening of terms left
implicit), conversion (an equivalence), the generic equivalence at `M`
(`geqM`, `gneM`) and the relations of the signature's components are
section variables, and what the development provides for them is a
hypothesis. The relation is left-indexed, as `IWfRel`:

```
MRn 0     w m t t' := geqM w m t t'
MRn (n+1) w m t t' := geqM w m t t'
                    ∧ shR w m (fst (out t)) (fst (out t'))
                    ∧ ∀ w' ≥ w, ∀ p p', posR w' m (fst (out t)) p p' →
                        MRn n w' (o[m, fst (out t), p]) (snd (out t) p) (snd (out t') p')
MR w m t t' := ∀ n, MRn n w m t t'
```

Checked (no admits, no axioms):
- `MR_escape`: the depth-0 clause.
- A Kripke PER closed under conversion and under a related index change:
  `MRn_mono`, `MRn_conv`, `MRn_idx`, `MRn_sym`, `MRn_trans` (and their
  `MR_` forms). Symmetry and transitivity move the right side's positions
  to the left shape (`pos_sh`) and the child indices along `o`'s
  relation; they need the index related to itself, which the type's
  relation gives.
- `MR_ne`: neutrals, by induction on the depth, from `out`'s neutral
  laws.
- `MR_out`: related trees have related shapes and children related at
  *every* depth. The depth quantifier moves inside the Kripke and
  position quantifiers, so `out t ~ out t'` holds at
  `Σ(s : S[m]). Π(p). M(o)` with the full relation at the child, which is
  what `SigRel`/`PiRel` need.
- `MR_corec`: for related indices and seeds related by the carrier's
  relation, the two `corec`s are related, by induction on the depth with
  the index and the seed generalized. The step's validity is read at the
  step type: on `inl y` (a new seed) the induction hypothesis at the child
  index, on `inr t` (an existing tree) `M`'s full relation there, on a
  neutral `case`'s neutral law and `MR_ne`. β and `case`'s β are
  conversions. The carrier's relation `X` is a premise of this lemma
  only; it is never part of the relation.

What each hypothesis is in the development (for M18b):

| probe | development |
|---|---|
| `le`, `*_mono` | `kwk`, `kw_comp`; the relations' weakening lemmas (`LogRel/Weakening.v`) |
| `conv`, `*_conv` | closure under typed weak-head expansion (`LogRel/Reduction.v`) and irrelevance at convertible types (`LR_irrel`) |
| `idxR`, `idx_*` | `LRiwf`'s index premise in every world, with its PER premises |
| `shR`, `sh_*`, `sh_idx` | the shapes' `domR` at an index, `LR` in every world at related indices |
| `posR`, `pos_*`, `pos_sh` | the positions' relation: `LR` at `P[m, s]` for related shapes, `codR`-style; `pos_sh` is irrelevance between `P[m, s]` and `P[m, s']` |
| `o_rel` | `LRiwf`'s premise on the child index, here at related positions of `P` |
| `geqM`, `gneM`, `geq_*` | `≈`/`~` at `M(m)` and `GenericEqLaws`; `geq_idx` is `geq_tm_conv` along `M`'s congruence |
| `gne_fstout`, `gne_kid` | `gne_tm_fst`/`gne_tm_snd`/`gne_tm_app` after a new `gne_tm_out`, and `LR_neutral` at `S[m]` |
| `beta_fst`, `beta_kid`, `case_inl`, `case_inr` | the reductions `out(corec) ⇝ …`, `fst`/`snd` of a pair, `app` of a λ, `case` of `inl`/`inr`, typed (subject reduction) |
| `case_ne` | `case`'s neutral law (`gne_tm_case`) at the constant motive `M(i)` |
| `geq_corec` | the new generic law `geq_tm_corec` (the kernel's `corec` arm) with the escapes of `X`, `c` and `x`'s validity |
| `step_valid` | the fundamental theorem's hypothesis for `c` at related substitutions, read through `SigRel`, `PiRel` and `SumRel` |
| `X`, `X_mono` | the fundamental theorem's hypothesis for `X` at its level `k` |

Not checked by the probes (the in-tree round's work, with no new kind of
argument): the syntax and its substitution and renaming lemmas, the
annotation variants (every choice of equivalent annotations on the
projections, as `SigRel` and `WNf` quantify), the typing of the reduct
(presupposition, subject reduction), injectivity of `M`, level
invariance, and the algorithm's PER and decidability proofs.

## Q1: the relation at `M`

**It is a per-former case.** `MRn` is a `Fixpoint` on the depth over the
components' relations, so `LRm` is a new constructor of `LR` with
`LRiwf`'s premises minus the arity (the index type in every world with
its PER premises, the shapes at related indices, the positions at related
shapes, the child index at related positions, the index) and
`releq R (MR …)`. It mentions no other case and no carrier, and needs no
change to the reducibility universe. The ω-intersection is a plain
definition in `Prop`, so no `CoInductive` and no guard checker are
involved, as the design asks.

**The generic clause at every depth is necessary.** Without it, `MR`
relates `zeros_u` and `zeros_n` (`MCoind.v`: same approximations at every
depth), escape would make them generically equal, and at the algorithmic
instance that is the kernel's `two_corecs_of_one_tree_are_distinct`
contradicted. With it, escape is the depth-0 clause, and the observations
are what `out`'s validity needs (`MR_out`). The neutral case and
`corec`'s case produce both halves (`MR_ne`, `MR_corec`).

**The positions' relation quantifies over every proof of the shapes'**,
as `WNf`'s children premise quantifies over `ha`. That is what lets the
depth quantifier move inside (`MR_out`): each depth's shape proof would
otherwise fix its own position relation. In the probe the position
relation does not depend on the proof at all, which is what irrelevance
gives.

**`li` must be in the family level.** The relation at level `f` is
`LR (lmeasure f) (LRbelow (lmeasure f))`, and a universe is related only
at a stage above it (`LRU`'s `lmeasure l1 < n`); a relation at a lower
level moves up a stage (`LogRel_stage`, `LogRel_up`) but never down. The
`M` case needs the index type's relation (the shapes are related at
related indices, and the fundamental theorem gets those from `S`'s
validity, which takes the index's relation), so `I @ li` must be related
at stage `lmeasure f`. Without `li` in `f`, `M(U_0; _. Unit; _ _. Empty;
…)(j)` would be a type at level 0 whose index type `U_0` has no relation
at stage 0. This is the architecture, not consistency: in a set model
`M(j)` is no bigger than its shapes and positions make it. So `l ⊔ l' ⊔
li` is the right choice for Heather, as `IWf`'s `l ⊔ li` is, and dropping
`li` later would mean changing the reducibility universe.

`corec`'s carrier is free (any `k`). Its relation is used only in the
fundamental theorem's `corec` case, at the carrier's own stage; the
step's validity lives at `lmeasure (l ⊔ k ⊔ f)`, and the `M(o)` summand's
relation there is `M`'s own (`LogRel_stage` keeps the relation).

## Q2: decidability and typed congruence

The algorithm of the design §2.1 needs two new generic laws and nothing
else, and both are the kernel's arms:

- `geq_tm_corec`: at `M(σ)(j)`, `k ≡ k'`, `X ≈ X'` under `i : I`,
  `c ≈ c'` at the left step type under `i, x : X`, `x ≈ x'` at `X[j]`.
  It is `MR_corec`'s `geq_corec`.
- `gne_tm_out`: `ν ~ ν' : M(σ)(j)` gives `out(ν) ~ out(ν')` at `out`'s
  type. With `Σ`'s neutral laws it gives `gne_fstout`/`gne_kid`.

Completeness is the fundamental theorem at the algorithmic instance, as
for every former; `MR`'s generic clause is what carries it through `M`.
"A `corec` against anything else is NotConvertible" needs no law: the
algorithm has no rule relating them, and completeness shows no
declarative equation does either (it would have an algorithmic
derivation). Decidability goes by induction on the left side's reflexive
derivation, as `actmnf_supi`'s: a `corec`'s premises are its carrier,
step and seed, all subterms, and no rule unfolds a `corec` outside an
`out` the term contains.

Typed congruence (`ELIM_CONGRUENCE.md`): the forced annotations are
forced as for the other formers, through an injectivity lemma `M_inj_c`
(the type's relation records the components' equations, as `LRiwf`'s
does). For `corec` the signature and index of each side are those of its
synthesized type, equal to the checking type's by inversion and
`M_inj_c`. The carrier's level is compared, for the reason the motive's
level is (`ac_ty`'s soundness is at one level). For `out` the scrutinees
determine everything, as at `elim_IWf`. A nit, not a bug: the kernel's
`corec` arm (`conv.rs`) says "the type's own [signature] is used", but it
builds the step type from the left `corec`'s signature (`g1`); under
typing the two are convertible, and either telescope is the same
judgement (`ELIM_CONGRUENCE.md`, "The motives and branches are compared
in the left elimination's telescope").

**β at an open, computed child index is sound with no index argument.**
The reduct's child is `corec(…; o[j, fst r, p]; y)` with
`y : X[o[j, fst r, p]]` from the step's type at `j`, and `out`'s type at
the shape `fst r` asks for `M(o[j, fst r, p])`: the same term. Unlike
`elim_IWf`'s β (M17b, "Preservation at any index", which needed the
`sup_i`'s output index converted to the eliminator's), nothing here is
read off a constructor. The one conversion subject reduction needs is
between `out`'s annotations and the `corec`'s, by inversion and `M_inj_c`
(the kernel's reducers use the `corec`'s, `reduce.rs` and `eval.rs`'s
`fire_out`). `MCoind.out_corec` has Rocq check the reduct's typing at an
open index.

## Q3: the bridge

Checked in `MCoind.v` for the unindexed former (the ITree case): left to
right by induction, right to left by `corec` under `UIP_S`, discharged by
decidable equality. For Heather: `Bisim` with `Id` shapes (the design §4)
gets the bridge exactly when the shapes form a set; with Heather's
no-UIP model (`H/docs/no-uip-model.md`) that is a hypothesis on the
event types (commands and answers with decidable equality, say), never
free. `Validity/Hedberg.v` has Hedberg's argument in this syntax. If a
`Bisim` is ever stated with `sEq` shapes, its per-depth proofs would be
convertible and the merge would need nothing, but `sEq` has no eliminator
to move the positions with (the design §4), so `Id` it is.

## M18b: the former in-tree (plan)

The plan as written before the work; the outcome follows it.

At layers D and M, M17b's route. Syntax: `tyM l l' li I S P O j`,
`tmCorec l l' li I S P O k X c j x`, `tmOut l l' li I S P O j m`, the
signature's scopes as `IWf`'s (`S` under one binder, `P` under two, `O`
under three; `X` under one, `c` under two). Reduction
`red_out_corec` with `m_out_corec`'s reduct (the step type `mStepTy` and
the out type `mOutTy` as definitions, as `iwfstepty`), `out`'s congruence
on its scrutinee, `whne_out`. Rules: `wft_M`, `wf_corec`, `wf_out`,
`eqty_M`, `eqtm_corec` (congruence, carrier level included),
`eqtm_out`, `eqtm_out_corec` (β), all gated by `compt i`.

Then, in M17b's order: presupposition (the reduct's typing:
`PresupM.v`), the relation (`LRm` over `MRn`, the probe's definition at
the development's annotations), escape, irrelevance, symmetry,
transitivity, weakening, level invariance, neutrals (`MR_ne`), validity
(`Validity/M.v`: formation, `out`; `Validity/MCorec.v`: `MR_corec` with
the step's validity), the algorithm (`actmnf_corec`, `actmne_out`) and
decidability (`AlgDecM.v`), canonicity (a closed term at `M` reduces to a
`corec`), and the consequences. Expected cost: below M17b, since the
relation is one `Fixpoint` rather than three mutual families and there is
no `dnth`; the widest piece is `corec`'s telescope in the generic laws'
annotation variants.

## M18b outcome

Done, no admits or axioms (`Print Assumptions` of `ac_dec_all`,
`decl_eqtm_dec_any`, `red_sound_all`, `closed_canonicity` and
`consistency` is empty). `M`, `corec`, `out` and β hold at layers D and
M through the relation, validity, the fundamental theorem, the
algorithm, decidability, the type checker and the consequences. **No
kernel rule is wrong**: every rule went in as Heather has it, the
annotations included. Files:
- `LogRel/Def.v`: `LRm` over `MRn` (the probe's definition at the
  development's annotations: `MGen`, the generic clause, at every depth;
  `MObs`, `out`'s observations through `SigRel` and `PiRel` themselves).
  `LogRel/MAux.v` has the Kripke-world syntax, `kw_eqv` (below, since
  removed) and
  `MSide`, what one `LRm` gives about its two signatures in every world;
  the rest of `LogRel` has one case each.
- `LogRel/MIdx.v`: `MRn_idx` (below).
- `Typing/PresupM.v`: the signature `MSig`, its equations `MEq`, the step
  type and `out`'s type well formed and equal along equal signatures,
  the β-reduct typed (`pre_out_corec`).
- `Validity/RelIntro.v`: `PiRel_intro`, `SigRel_intro` (below).
- `Validity/M.v` (formation, `out`), `Validity/MStepV.v` (the step type's
  and `out`'s type's validity), `Validity/MCorec.v` (β's reduct in pieces,
  typed and related), `Validity/MCorecV.v` (`corec`'s depth induction).
- `Validity/AlgDecM.v`: the decision cases, a part of its own.

Decisions and deviations, in the order the proof met them:
- **The relation is two-sided and proof-free.** Both signatures and both
  indices are `MRn`'s arguments and the shapes' and positions'
  relations are indexed by both sides, so symmetry is a flip of the
  arguments (`MRn_flip`). The relations take no proofs of the index's or
  the shapes' relation: the canonical relations validity uses (`LRrel`)
  do not, so the positions premise's quantification over proofs (Q1) is
  not needed in-tree.
- **The observations are made in every world, with the annotations in
  the world's context** (`MObs` quantifies over `MAnn`, `out`'s
  annotations declaratively equal to the signature's). A weakened tree's
  `out` may carry annotations that are not a weakening, and moving
  `Σ`'s relation between two `out`s' annotations at a neutral scrutinee
  would need reflection of neutrals, which comes after weakening.
- **Worlds compose associatively only up to `kw_eqv`** (as built in
  M18b; superseded by "Associative worlds" below). Two worlds were
  equivalent when they had the same contexts and acted alike on types,
  terms and local renamings; both associations of a composite, and a
  world after the identity, were. The shapes' and positions' relations
  respected it (`MSide`'s invariance fields, `LR_kw_eqv`), so each child
  in `corec`'s depth induction took one conversion step.
- **`corec` is related at its own index, then moved to the claimed one.**
  `MRn_idx` (`MIdx.v`) moves `MRn n` at indices `m, m'` to any indices
  related to them, by `MRn_dir` on the right index and `MRn_flip` around
  it on the left. The depth induction (`MCorecV.v`) proves its statement
  only at the `corec`'s own index `j[d]`, where the step's validity
  speaks, and the claimed child indices `o[j, a, p]` go through
  `MRn_idx` once, instead of stating every fact twice and bridging.
- **`Π`'s and `Σ`'s relations from their Kripke clauses** (`RelIntro.v`).
  `out`'s observations are a `Σ` of a `Π` at relations that are not
  `LR`'s; `PiRel_intro` and `SigRel_intro` give the generic equality the
  relations ask for from the clause (extensionality at the variable, and
  by the projections), the argument `V_lam` and `V_pair` make inline.
- **`corec`'s and `out`'s rules have only their premises.** The step
  type's validity (the two sides' step types related) is built in
  `MStepV.v` from `Σ`, `Π`, `+` and `M` at the signature weakened past
  the step's binders; `out`'s type's is read off `LR_out_kw` in the
  identity world. Neither type is a premise of a rule, as in Heather.
- **The algorithm's annotations as designed (Q2).** `actmnf_corec`
  compares carrier level, carrier, step at the left step type and seed,
  the signature and index read off the type; `actmne_out` compares the
  scrutinees only, and its inferred type is the left `out`'s. Soundness
  relates the annotations through `M_inj_c`, and `corec_parts` /
  `corec_right` move a `corec`'s pieces, and the other side's, to the
  type's telescope (`AlgSound.v`); every later part of the algorithm
  uses those two lemmas.
- **Canonicity's case is the plain one.** A closed term at `M` computes to
  a `corec` (`canon_head` at `M`'s head), which the existing theorem
  needed once `corec` was a whnf. Canonicity and productivity at `M`
  proper are heather-coq#39, after M18b.
- **Preservation at any annotations.** β fires at a `corec` of any
  annotations under an `out` of any; `RS_out_corec` relates the two by
  `M_inj_c` and applies the declarative β at the `corec`'s.
- **Build notes.** `FundamentalM`'s rule dispatch passes its side tactic
  delayed (`vs_rules ltac:(idtac; m_side)`): passed bare, Ltac ran it at
  the call and the dispatch failed on goals it closed delayed. Its
  rewrite pass gained a `tyM` trigger, so `out`'s type's lifted single
  substitutions are pushed through the semantic substitution, as `GLift`'s
  `gwa` push now is (`MAux.gwa_llift_single_ty`). Three section proofs
  (`UPiV`'s `VS_red`, two in `FundamentalM`) now name `ELP` in their
  `Proof using`, by Coq's own suggestion.

Follow-ups:
- **Associative world composition.** Done (heather-coq#61): "Associative
  worlds" below.
- **Canonicity and productivity at `M`** (heather-coq#39), as planned,
  now that the former is in-tree.

## Associative worlds (heather-coq#61, after M18b)

Kripke worlds (`kwk`, `LogRel/Def.v`) now compose associatively, and the
identity world is a unit on both sides, by `eq_refl`:
`kw_comp_assoc`, `kw_comp_id_l` and `kw_comp_id_r` are `reflexivity`, so
`idxR (kw_comp (kw_comp ρ ρ') ρ'')` and `idxR (kw_comp ρ (kw_comp ρ' ρ''))`
are one proposition and nothing moves between them.

**Representation.** A world over `(G, Γ)` stores what it does to a later
world rather than its own data:
- `kw_gk : gweak -> gweak` and `kw_rk : wk -> wk`, a later weakening
  followed by the world's own (`kw_gk γ0` is `γ0` after `γ`);
- `kw_gokk` and `kw_wfk`, its two well-formedness proofs as transformers
  of a later world's (`gwk_ok γ0 G' (kw_G ρ) -> gwk_ok (kw_gk γ0) G' G`,
  and likewise for the local OPE);
- `kw_gcoh`/`kw_rcoh`: the maps are composition with the data
  (`kw_gk γ0 = gwk_comp γ0 (kw_gk gwk_id)`), boxed into `SProp` (`SBox`);
- `kw_G`, `kw_Δ`, `kw_ctx` as before.

`kw_comp` is then function composition in every field but the coherence
ones, which are in `SProp` and so convertible whatever their proofs; the
record has primitive projections, so a world is its own η-expansion and
the identity world (`kw_id`, `kw_self` is now it) is a unit by β and η.
The plain data are definitions: `kw_γ ρ := kw_gk ρ gwk_id`,
`kw_r ρ := kw_rk ρ wk_id`, `kw_gok`, `kw_wf`, at their old types, so every
statement over worlds reads as before. The composite's data are
propositional (`kw_γ_comp`, `kw_r_comp`), from the coherence: the
equations on `gweak`/`wk` are decidable, so `sunbox` gets them back out
of `SProp` without an axiom. `kw_mk` builds a world from data and proofs
(the old constructor's signature); `kw_loc` and `kw_mk` compute their
data at the identity by a `match`, so `unfold kw_loc; cbn [kw_γ kw_gk
kw_r kw_rk]` gives the data as before.

**Why this shape.** Composition of the first-order OPEs (`gwk_comp`,
`wk_comp`) is associative only by induction, and the proof fields of
the old record (`gwk_ok_comp …`, `kw_comp_wf …`) differ between the two
associations. Representations that compose by function composition are
definitionally associative; the proofs become transformers composed the
same way (a pair of them would need a commuting conversion of the
`match`es, so they are two fields). Storing the plain proofs in `SProp`
instead would need `wk_wf` and `gwk_ok` decidable, which needs decidable
equality of the whole syntax; only the coherence goes to `SProp`, and
its equations are over `gweak`/`wk`, whose equality `decide equality`
gives. No axiom: `Print Assumptions` of the main theorems is still empty.

**What went.** `kw_eqv` and its lemmas (`MAux.v`), `MSide`'s three
invariance fields and `MSide_intro`'s premises (one `MSide_of_LR` is
left), `LR_kw_eqv`, `LR_kw_eqv_irrel`, `mSh_eqv`/`mPos_eqv`, `mrn_eqv`,
`kw_eqv_trans`; `corec`'s depth induction (`pair_at`, `corec_all`,
`V_corec`) now closes its children by `exact`. Beyond `M`, the same
reassociation was in `W`, `Wf` and `IWf`: `WNf_kw`, `WfNf_kw`, `IWfNf_kw`
and their `*Rel_kw` lose their premises relating the relations at the
two associations, `Weakening`'s `W`/`Wf`/`IWf` cases no longer prove
them by irrelevance, and the spine lemmas (`Wf.v`, `IWfSp.v`, `WfElim.v`)
no longer move along `WfDom_assoc`/`KDom_assoc` (removed). In all, the
theories lose about 180 lines net (the representation adds about 120,
most of them `kw_gk kw_rk kw_mk` added to `cbn` lists; the removals
are about 300).

**Time.** Clean builds of the base (`eb7e28d`) and this branch, back to
back at -j4 on one 4-core cloud machine (`tools/build-profile --clean`):
1584 s and 1476 s wall, 3787 s and 3610 s CPU. The difference is
drift, not the change: files the change does not touch moved by up to
25 % between the runs, in both directions (`Typing/TypedDnf` 119 s →
143 s, `Validity/DVecNthReds`'s example 132 s → 108 s). The 15 files
the change touches take about 100 s of CPU together (97 s → 79 s), so
whatever it saves in proof time is below what one build-to-build
comparison can see; the saving is in proof size and in what later
formers no longer have to state.

**For later formers.** A Kripke clause at a composite world needs no
invariance premise: state it at `kw_comp ρ ρ'` and use it at either
association. To read a world's data, rewrite with `kw_γ_comp`/`kw_r_comp`
(a `cbn` exposes `kw_gk ρ (kw_gk ρ' gwk_id)` instead); a `cbn` list that
should reduce `kw_γ`/`kw_r` of a built world names `kw_gk`/`kw_rk` (and
`kw_mk` for a world `kw_mk` builds) too, as primitive projections reduce
under `cbn [...]` only when listed (`docs/gotchas.md`).

## M18c: codes (plan)

When Heather's codes round gives `M` its four branches (the design §5:
`ty_m`, `tm_m`, `tm_corec`, `tm_out`), derive their scopes from the
layer-C rules here first, as M17c did for `IWf`.
