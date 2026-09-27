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
- `pair (l l' : lvl) (A B : ty) (a b : tm)`: `B` binds one local.
- `fst (l l' : lvl) (A B : ty) (p : tm)` and `snd (l l' : lvl) (A B : ty)
  (p : tm)`: `B` binds one local.

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
- `geq_tm_pair`: the pair congruence (the relation's whnf equality for
  pairs);
- `gne_tm_fst`, `gne_tm_snd`: neutral projections.

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

(filled in as the steps land)

## Status

Design written; step 1 in progress.
