# Milestone 8: Σ and Unit (Heather's extensions, first round)

Goal: add Heather's dependent pairs with definitional η, then its
level-indexed Unit with η as proof irrelevance
(`H/docs/delam-extensions.md` §6, §7; `HEATHER.md`). Both go through the
whole stack: syntax, typing and metatheory, generic laws, the relation,
semantic rules and the fundamental theorems, algorithmic conversion, type
checking, and consequences. We also record what each former costs, to
decide how to make the development more generic (`HEATHER.md`, "Making
this repo easier to extend").

Heather references: `H/crates/kernel/DESIGN.md` (§Fragment, second and
third extension), `H/docs/delam-extensions.md` §6 (Σ), §7 (Unit, Empty),
§11 (the two η rules), `H/docs/metatheory-ch07-extensions.md` §3 (Σ),
§4 (Unit).

## Scope and staging

| Stage | Contents |
|---|---|
| **M8a** | Σ at layers D and M: syntax, rules, metatheory, relation, FTs, algorithmic conversion, type checking, consequences |
| M8b | decide the genericity direction, using M8a's measurements |
| M8c | Unit at layers D and M, the same way |
| M8d | Σ and Unit as code: the rules at layer C, and the recursor branches (Heather's `ty_sigma`, `tm_sigma`, `tm_pair`, `tm_fst`, `tm_snd`, `ty_unit`, `tm_unit`, `tm_triv`: 13 → 21) |

### I1. The new formers are gated to layers D and M first (default taken)

Heather has Σ and Unit at layer C, so they are code and the recursors
have branches for them. That costs eight new recursor branches, and the
recursor is our largest per-branch cost (`RecS.v` alone is 3.4k lines for
13 branches). So M8a/M8c gate every new rule by `compt i`, as the
computation rules are already gated, and M8d lifts the gate.

This is coherent without any recursor change:
- no layer-C derivation contains the new syntax (every C rule's
  subderivations are at C, apart from the types at `typeof C = D` that
  terms carry in their typing but not in their syntax);
- the recursor's branches that receive a D-type (`U_T` of the variable
  branch 4 and of the `λ` branch 11, `gdTy … lD …`) already accept any
  D-type, so code whose *type* is a Σ (a variable, or a `λ` whose body
  has Σ type) is handled by the existing branches;
- the C-typed inductions (Static Code, `FundamentalS` at C, the recursion
  lemmas) get new cases that are vacuous (`compt lC` is false).

Heather used the same staging for `Vec`/`Fin`/`Wf` (its "phase gate").
Recorded as a departure from Heather until M8d.

## Decisions (M8a: Σ)

### I2. Syntax: fully annotated, as `app`

- `tySig (l l' : lvl) (A B : ty)`: `Σ^{l,l'} x:A. B`, `B` binds one local.
  Lives at `lmax l l'`.
- `tmSig (l l' : lvl) (s t : tm)`: its code, `t` binds one local; decodes
  as `El (l⊔l') (Σ s t) ≅ Σ (El l s) (El l' t)`.
- `tmPair (l l' : lvl) (A B : ty) (a b : tm)`: `B` binds one local.
- `tmFst (l l' : lvl) (A B : ty) (p : tm)` and `tmSnd (l l' : lvl) (A B : ty)
  (p : tm)`: `B` binds one local. (Below, `pair`/`fst`/`snd` for short.)

Annotations are sub-structure, as the recursor branches of M8d need
(Heather: "fully annotated … so they infer"). Reduction ignores them
(M1 deviation, as for `app`).

### I3. Typing (all gated by `compt i`)

Formation, code, introduction and elimination:
- `wft_sig`: `A @ l`, `Γ, A @ l ⊢ B @ l'` ⟹ `tySig l l' A B @ lmax l l'`;
- `wf_code_sig`, like `wf_code_pi`;
- `wf_pair`: `A @ l`, `Γ, A ⊢ B @ l'`, `a : A @ l`, `b : B[a] @ l'` ⟹
  `pair l l' A B a b : tySig l l' A B @ lmax l l'`;
- `wf_fst`: `A`, `B`, `p : tySig l l' A B` ⟹ `fst l l' A B p : A @ l`;
- `wf_snd`: the same premises ⟹ `snd l l' A B p : B[fst l l' A B p] @ l'`.

Equations: the congruences `eqty_sig`, `eqtm_code_sig`, `eqtm_pair`,
`eqtm_fst`, `eqtm_snd`, shaped like the Π ones (left side typed, levels
up to `≡`); `eqty_El_sig`; β:
- `eqtm_fst_beta`: `fst l l' A B (pair l l' A B a b) ≅ a : A @ l`;
- `eqtm_snd_beta`: `snd l l' A B (pair l l' A B a b) ≅ b : B[a] @ l'`;
and η as **surjective pairing** (Heather ext §6.6, the paper-shaped form
of our Π η):
- `eqtm_sig_eta`: `pair l l' A B (fst l l' A B p) (snd l l' A B p) ≅ p
  : tySig l l' A B @ lmax l l'`.

The extensional form (`fst p ≅ fst q`, `snd p ≅ snd q` ⟹ `p ≅ q`) is a
lemma, and it is what the generic laws state (I5).

### I4. Reduction and normal forms

`fst l l' A B (pair …  a b) ⤳ a`, `snd … (pair … a b) ⤳ b` (annotations
ignored), and `fst`/`snd` reduce in their scrutinee. `tySig`, `tmSig`
and `pair` are whnf; `fst ν`, `snd ν` are neutral.

### I5. Generic laws

Added to `GenericEq`:
- `geq_ty_sig`, `geq_tm_code_sig`: congruences;
- `geq_tm_sig_ext`: `fst p ≈ fst q : A` and `snd p ≈ snd q : B[fst p]`
  ⟹ `p ≈ q : Σ` (the extensionality form; the algorithmic instance
  compares projections at Σ, as it η-expands at Π);
- `gne_tm_fst`, `gne_tm_snd`: neutral projections.

No pair congruence law was needed: the relation compares Σ terms through
their projections only, so a pair is never compared as a whnf.

### I6. The relation: `LRsig`

Shaped like `LRpi`: Kripke domain relation `domR` and codomain relation
`codR` (instantiated at related arguments), generic equality of the
domains and codomains. The term relation `SigRel`: both sides reduce to
whnf, the whnfs are generically equal, and in every weakening and for
every choice of equivalent annotations on the projections
- the first projections are related by `domR`,
- the second projections are related by `codR` at some proof of the
  first projections' relation.

Kripke quantification in the term relation mirrors `PiRel` and makes
weakening immediate.

### I7. Semantic rules

`Validity/Sigma.v`: formation, code and decoding, pair, projections, β by
anti-reduction, η from the projections' β at every instance.

### I8. Algorithmic conversion

- Types: `actnf_sig`, structural like `actnf_pi`; codes `actmnf_code_sig`.
- Terms at a Σ type: `actmnf_sig_eta` compares `fst l l' A B w` at `A`
  and `snd l l' A B w` at `B[fst l l' A B w]`, the annotations read off
  the type (as Π's η takes them).
- Neutral projections: `actmne_fst`/`actmne_snd` ignore their own
  annotations (as `actmne_app` does) and read the result type off the
  scrutinee's inferred `Σ m m' A0 B0`. For `snd` this is
  `B0[fst m m' A0 B0 ν]`, the left scrutinee's first projection at the
  *inferred* annotations, so the result type does not depend on the
  node's annotations either.

**Annotation changes (H10 revisited).** M6 closed the algorithm under
changing the annotations of the head spine (`spa`) by a syntactic
induction at a fixed type. That fails with Σ: the type of a second
projection mentions its scrutinee, whose spine annotations `spa` changes
(`snd (app w↑ …)` at `D[fst (app w↑ …)]`, when Π-η meets Σ-η). So `spa`
now lives in `AlgConv` as a *typed* relation: each changed node carries
the equations of its annotations (as the congruence rules need them), it
extends through `tmFst`/`tmSnd`, and the conversion lemma carries it on
its term motives (`C_tm` … `C_nee` take targets `x x'` with `spa t x`,
`spa t' x'`). The types then move up to declarative equality, which the
conversion lemma already allows, using `spa_eq` (related typed terms are
equal). The old statement is the corollary `ac_conv_all` (targets =
sources). Weakening lemmas `spa_wk`, `spa_uwk`, `spa_gext` serve the four
η rules.

## Order of work (M8a)

1. Syntax: constructors, every operation and law, `≡ₗ`, normal forms,
   reduction.
2. Typing: the rules and every metatheory lemma.
3. Generic laws and the declarative instance.
4. The relation: `LRsig` and every `LR` property.
5. Semantic rules and the fundamental theorems.
6. Algorithmic conversion (M6) and type checking (M7 C1).
7. Consequences: normalization, canonicity, injectivity, discrimination.

Record per step: the files touched and why, for M8b.

## Cost log (for M8b)

M8a Σ, from the design commit to the finished algorithmic side: 56 files,
about 4000 lines added, 330 changed.

| Area | Files | Lines added |
|---|---|---|
| Syntax (operations, normal forms, reduction, commutations) | 7 | 117 |
| Typing (rules, weakenings, substitutions, presupposition, inversion, static code, algorithmic rules and closure) | 16 | 815 |
| LogRel (the Σ case of every relation property) | 12 | 773 |
| Validity (semantic rules `Sigma.v` 863, FTs, consequences, algorithmic soundness, conversion, PER, lift, instance, decidability, type checking) | 21 | 2308 |

Observations:
- Most per-former cost is *boilerplate replicated per judgment family*:
  each of the five structural families of `AlgStruct` (W/G/U/L), and each
  of soundness, conversion, symmetry, transitivity and decidability, wants
  one lemma per algorithmic rule, 5 rules for Σ. They follow the Π
  templates almost verbatim (renaming `pi` to `sig`), which is what a
  generic treatment should remove.
- Positional intro patterns over the relation's constructors broke in
  every `LR` induction (scripted with `lrpat.py`); appended cases and
  dispatch lists kept the rest stable.
- The genuinely new mathematics was small: `SigRel` and its Kripke
  shape, `Sigma.v`, and the typed `spa` (I8).

## M8b: the genericity direction

### Where the cost is

Σ's lines by kind (`git diff --stat 05ff08f c6b86c2`):

| Kind | Lines | Generic? |
|---|---|---|
| New mathematics: rules, `SigRel`, `Sigma.v`, typed `spa` | ~1.3k | no (`Sigma.v` is the size of Π's five semantic files together) |
| Per-*rule* cases of inductions over judgments: typing metatheory, `AlgStruct` W/G/U/L, soundness, conversion, PER, decidability | ~1.8k | mostly: W/G/U/L are one script with a different push tactic |
| Per-*former* cases of inductions over `LR` | ~0.8k | partly: Π and Σ share the type-level half; positional patterns are pure churn |
| Syntax | 0.1k | not worth it |

The largest *future* cost is the recursor. Heather has 56 branches
(derived from telescope specs, `H/crates/kernel/src/rec.rs`
`branch_specs`); we have 13, hand-written, at 100–250 lines per branch
in `RecS.v` alone, plus the other `Rec*` files.

### J1. Decisions (taken)

In order, cheapest first:

1. **Tactics, not per-rule lemmas.** Each family (W/G/U/L, S, C, Y, T,
   Dc, and the typing metatheory inductions) gets a closing tactic run on
   every case of its mutual induction; named lemmas remain only for the
   cases the tactic does not close. Applies to every future former,
   positive or negative, and removes existing Π-era code too. Spike first
   on `AlgStruct`'s W family to measure coverage and build time.
2. **Record-packed `LR` cases** (logrel-coq style): each constructor
   takes its data as one record, so adding a former no longer edits
   positional patterns across a dozen files. Π and Σ then share the
   domain/codomain record (logrel-coq's `PolyRed`/`ParamRedTy`), which W
   and `Wf` will reuse.
3. **Recursor branches from telescope descriptions.** A branch is
   described by its sub-structures (kind, context extension, level,
   index); `redT`/`redt` become one generic peel along the telescope, and
   the `RecS` recursion lemma is proved once over descriptions (`br_core`
   already factors part of this). Needs a design pass against Heather's
   `branch_specs` before M8d.

Not done: a generic binding signature or a binder-kind syntax
(`tyBind Π|Σ`). It would undo the hand-written syntax decision
(`SYNTAX_SPIKE.md`) to save about a hundred lines, the per-former parts
(`PiRel` vs `SigRel`, the η forms) stay separate anyway, and logrel-coq
does not do it either.

Acceptance test: Unit (M8c) should then cost little beyond its own
mathematics, measured against the Σ cost log.

### J1 log

- **Step 1, `AlgStruct` (W/G/U/L).** Each family is one tactic
  (`W_case`, `G_case`, `U_case`, `L_case`) run on every case of `ac_mut`:
  push the operation through the goal; instantiate each induction
  hypothesis at the scope that reaches its context (`mk_wkr`, `mk_gwk`,
  or by the shape of its global context for U) and normalize it once;
  `econstructor`, closing judgment premises first (they fix the evars
  side conditions share), then side conditions. Named lemmas remain only
  for irregular premises: substitution entries (`G_acs_pt`, `U_acs_pt`,
  `L_acs_pt`), recursor branches (`*_branches`), `uapp`'s level
  instantiation (`U_actmne_uapp`), and the reductions under `≡ₗ`
  (`L_act_red`, `L_actm_red`). 1566 → 515 lines; all 180 rule cases,
  Σ's included, close without per-rule code. Build time of the file
  8.6 s → 12.2 s, dominated by the existing `push_gren` rewrite chain.
  Lesson: normalizing hypotheses per premise (1090 calls) cost 10 s;
  once per case, 70 calls.
- **Finding for the other families.** Soundness, conversion, symmetry,
  transitivity and decidability do not share this shape: a case inverts
  both sides' typings, relates the annotations, moves the right premises
  into the left context (`stab_*`, `cv_*`) and applies a declarative
  congruence. What repeats there is not "every rule" but "every rule of a
  shape": `Y_actnf_sig` is `Y_actnf_pi` with `pi` renamed, and likewise
  the code rules, in all five families. The tool for that is a generic
  lemma per shape (a binder type former, a binder code), taking the
  former's inversion, congruence and algorithmic rule as arguments, with
  Π and Σ (and later W) as one-line instances. It does not help
  non-binder formers such as Unit, whose cases there are small anyway.
- **Step 2, the relation (`LogRel`, `Pi.v`/`Sigma.v`).** `LRpi` and
  `LRsig` take their thirteen type-level facts as one record,
  `PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B'`, parameterized by the
  former `F`. The domain and codomain derivations stay direct constructor
  arguments, so Coq's generated induction principle keeps their induction
  hypotheses (a record containing `LR` would be a nested inductive and
  lose them). Patterns bracket the record (`[Hl … HBB]`), so proofs that
  only pass the facts through kept their names; `open_poly` exposes them
  where the case is unnamed. The inversions `LR_inv_pi`/`LR_inv_sig`
  return the record. Shared, once for any `F`: `poly_flip` (symmetry),
  `poly_trans` (transitivity), `poly_kw` (Kripke weakening, given `F`'s
  commutation with it), `poly_pg` (universe permutations, likewise),
  `poly_here` (the validity side's type relation with Π's domain and
  codomain relations, given `F`'s formation rule and substitution
  commutation), and the Ltac `poly_irrel` (irrelevance). Net lines about
  zero (376 added, 381 removed): the shared lemmas replace the Σ copies,
  so the next binder former (W, `Wf`) pays only instances. Not shared:
  level invariance, whose Π case is 240 lines of mostly term-level
  reasoning reusing its intermediate facts, so a `poly_leq` would remove
  only the thirteen construction bullets. The term relations (`PiRel`,
  `SigRel`) and their lemmas are genuinely per former.

## Status

M8a (Σ) complete: syntax, typing and metatheory, generic laws and both
instances, the relation, semantic rules, FTs at P and M, injectivity,
canonicity, preservation, type checking, algorithmic conversion with
soundness, conversion, PER, lift, completeness and decidability. No
admits; `consistency`, `tyd`/`ckd`, `ac_tm_dec` and
`decl_eqtm_dec_any` are closed. Next: M8b (genericity direction).
