# Milestone 2: global variables, static code, contextual types

Goal: extend M1 with the parts of DeLaM that make it modal. That means global
contexts that are actually used, global variables `U^δ`/`u^δ`, layer C
(static code), the contextual types `□` for types and terms (`CTyp_Δ l`,
`CTrm_Δ T l`), `box`, both `letbox`es with their β rules, the layered
logical relation (`j ∈ {P, M}`), Kripke quantification over global
weakenings, validity quantifying over related global substitutions, and one
fundamental theorem for every layer in {C, P, M}.

Paper references: ch. 4 (rules, 04:769–1626), ch. 5 (global substitutions
and the metatheory, 05:190–1498), ch. 6 (reduction), 07:48–398 (generic
laws), 07a (semantic global contexts, `⊩^{≥P}_P`, `⊩^C_P`, `j = M` cases,
Layering Restriction 07a:1057), 07b (semantic judgments and the FT). A
line-referenced digest of those chapters was made when this plan was written.
Its conclusions are recorded here.

## Scope and staging

| Stage | Contents |
|---|---|
| **M2** (this doc) | layer C; global bindings `U : DTyp^C_Δ l`, `u : DTrm^C_Δ T l` (plus `g : Ctx`, already present); `U^δ`, `u^δ`; `CTyp`, `CTrm`, `box`, `letbox_Typ`, `letbox_Trm` with β and congruences |
| M2b | `CΠ` (context abstraction/application) and `TΠ` (which also brings `DTyp^P` bindings). Their relation cases recurse into `j = M`, so they are real new `LR` constructors |
| M3 | the code recursors, layer V (only the recursors' variable branch needs it), the full inductive `⊩^C_P` record, universe polymorphism `UΠ` (the only use of ω and of universe weakenings θ) |

Why this cut: the digest found no dependency from `□`/`letbox` (relation
cases or FT cases) on `CΠ`, `TΠ` or the recursors. `letbox` only ever
extends a global substitution by `t''/u` (scrutinee `box t''`) or
`u^id/u` (neutral scrutinee). Without `UΠ`, the universe context `L` never
changes, so θ is the identity throughout and the paper's measure becomes
"`j`, then ℕ levels".

## Decisions

### D1. Syntax: additive constructors, spike laws for global operations

- New `ty`: `tyCTyp (Δ : ctx) (l : lvl)`, `tyCTrm (Δ : ctx) (T : ty) (l : lvl)`.
- New `tm`: `boxT (T : ty)`, `boxt (t : tm)`, `letboxT l' l Δ M t' t`,
  `letboxt l' l Δ T M t' t`. The motive `M` binds one local variable; `t'`
  binds one global variable.
- **Local substitution does not enter `box` and leaves the `Δ` of `□`
  alone** (05:125, 05:147). Global substitution enters everything.
- Global renaming (`ξ : nat -> nat`) and global substitution
  (`σ : nat -> gobj`, with `gobj ::= GId j | GCtx Γ | GTy T | GTm t`) are
  ported from `spike/Syntax.v` to the Tarski split. Instantiation is
  `U^δ[σ] = σ(U)[δ[σ]]`. A local substitution passing under a global binder
  is globally shifted (`gwk`). The spike's cross laws (`t[δ][σ] =
  t[σ][δ[σ]]`, the renaming versions, and letbox β commutation) are the
  targets.

### D2. Typed local substitutions become a judgment premise

The `u^δ`/`U^δ` rules need `Γ ⊢_i δ : Δ` as a premise inside the mutual
inductive. Its form is M1's lookup-based definition: context-tail and
length conditions plus `∀ n T l, in_ctx Δ n T l → Γ ⊢_i llk δ n :
T[δ] @ l`. This is strictly positive, and Coq's schemes generate the
functional IH. The equivalence version is analogous, with the paper's
redundant typing premises (04:1012). `lsub_wf` in `Typing/Substitution.v`
becomes a projection of this.

### D3. Layer C and the syntactic metatheory

M1's metatheory assumed `typeof i = i`. M2 needs, per ch. 5:
- **lifting** (`i ≤ i'` preserves judgments, 05:996);
- **unlifting** P→C for types and terms whose syntax is MLTT-only (05:1039);
- **Static Code** (05:1055): at C, equality is syntactic *modulo level
  equivalence*. Our levels carry semantic `≈`, so we define `≡ₗ`
  (syntactic equality with `lequiv` on every level annotation) and state
  Static Code with it. Everything that the paper phrases as "`t = t'`" for
  C-layer code (global substitution relation, the `box` clause) uses `≡ₗ`.
- substitution and presupposition extended to C;
- **global weakening** and the **global substitution lemma** (05:1075),
  the latter restricted to the P/M range for context statements;
- equivalent global substitutions, and global context equivalence.

### D4. Generic equivalence: one instance per layer

The relation uses the generic equivalence at both P and M (`⊩^{≥P}_P`
quantifies over `k ∈ {P, M}`). M1's machinery is parametric in one
`GenericEq` instance, so every M1 lemma already applies to each layer
separately. M2 adds:
- a **pair** `(EP, EM)` of instances with `ge_layer = lD` and `lM`, and the
  new laws. At M these are: type constructor laws for `CTyp`/`CTrm`, `box`
  congruence (reflexive), neutral `letbox`, and neutral global variables at
  both layers (07:233–277, 07:297–369);
- weakening laws for global weakenings;
- the declarative instance at `lD` and `lM`.

No cross-layer law is needed: the P and M relations interact only through
validity's quantifier over `k`.

### D5. The relation: a `j` index, a validity parameter, global Kripke

- `LR` gains an index `j` (`jP | jM`). The new constructors `LRctyp` and
  `LRctrm` carry a guard `j = jM`. The `j = P` relation is then literally
  the `j = M` relation minus two constructors, and the **Layering
  Restriction** (07a:1057) becomes a derivation map (`jP → jM`) that keeps
  `R` unchanged. With saturation it is a one-line induction.
- The `□` cases refer to `⊩^{≥P}_P` (related contexts and types at both
  layers under all global weakenings and related local substitutions) and
  to the static-code payload. Neither refers back to the `j = M` relation
  (07a:717). So `LR` takes them as a **parameter record** `vp`, like `rec`.
  The record holds context relatedness, type relatedness, and the payloads
  for code of types and code of terms, with a laws record (sym/trans,
  weakening). It is instantiated after the `j = P` relation is complete.
- **Static-code payload (the one real fork, see below):** in M2 the payload
  of `box T₁`/`box t₁` is `⊢_C` typing plus `⊩^{≥P}_P`, behind an
  interface. M3 replaces it with the paper's inductive `⊩^C_P` record
  (07a:118), which the recursors need.
- **Kripke over global weakenings γ.** `DomRel`/`CodRel`/`PiRel` quantify
  over `(G', γ, Δ, r)` with `γ : G' ≤ G` a global OPE and `r : Δ ≤ Γ⟨γ⟩`.
  M1's own design note predicted this: it changes `LRpi`/`PiRel` and the
  weakening lemmas, not the other cases. The global-weakening lemma for
  `LR` needs global renaming stability of reduction and of the generic
  relations.

### D6. Validity and the fundamental theorem

- `⊩ σ ≈ σ' ∈ Ψ` is a relation on global substitutions, by recursion on
  `Ψ` (like `SubRel`):
  - `g ↦` related contexts at `≥P`;
  - `U : DTyp^C ↦` `T ≡ₗ T'` with the static payload on both sides;
  - `u : DTrm^C ↦` `t ≡ₗ t'` with the payload.

  Stability under global weakening replaces the paper's θ-stability.
- `VTy/VTm` quantify over:
  - a global weakening;
  - related `σ σ'`;
  - `k ≥ i` (so at C, k ranges over C, P and M, and the `k = C` case is the
    static payload);
  - related local `δ δ'` at `k`.
- There is **one FT** over all judgments at C, P and M, proved in the order
  M, P, C (07b:216). The M1 FT becomes its `j = P`, `σ = id` fragment.

## Decisions taken while implementing (typing)

- **Seventh judgment `eq_ctx`** (`[G ⊢[i] Γ ≅ Γ']`), for the congruences of
  `□`. `typing_mut` gains a seventh component, appended last, so M1's
  positional projections of the first six stay valid.
- **Typed local substitutions carry the paper's tail condition**
  (`lsub_tail`, 04:990). Past the variables of the domain, `δ` is the
  shift by `|Γ|`, and both contexts end the same way. Lookup typing alone
  can't see how a context variable's own variables are sent, and global
  substitution of `g` would break. `lsub_wf` is now a record
  (`lsw_ctx/lsw_dnf/lsw_tail/lsw_var`), with its context at `typeof i`.
- **Normal forms:** `nf*` constrains only what local operations traverse
  (box contents and the `Δ`/`T` of `□`/`letbox` are ignored), so local
  outputs stay normal unconditionally. The *deep* forms `dnf*` include
  them. Global identity laws need `dnf`, typed terms are `dnf`
  (`typed_dnf`), and the global-variable rules require `dnfl δ`.
- **Redundant well-formedness premises** (the M1 convention) were added where
  a proof otherwise needs a context fact that its premises only imply via
  presupposition:
  - `[Δ ⊢_P]` on the `box` rules, `wft_CTrm`/`eqty_CTrm`, and the
    `letbox` congruences/β-rules;
  - the second substitution of the `U^δ`/`u^δ` congruences is typed at its
    own type `A[δ']`, not at `A[δ]`. This is just as redundant, and
    functionality then needs no conversion.
- **`El`-decoding equations are gated by `compt i`.** The paper puts them at
  every layer but V (04:638), which contradicts its own Static Code Lemma
  (05:1055): at C, `Nat` and `El 0 ⌜Nat⌝` must stay distinct code. We
  follow the Static Code Lemma.
- **Metatheory at every layer:** global weakening, lifting, local
  weakening, and the substitution lemma are proved for all layers.
  Weakening/substitution use a target context at `typeof i` and lifting for
  context extensions. The `letbox` body is handled by global weakening by
  one binding (`gwk d` under the binder). The M1 statements (`typeof i =
  i`) are kept as corollaries.
- **Global substitution lemma** (`Typing/GSubstitution.v`, all layers,
  all judgments). `[G' ⊢ σ : G]` sends each binding to an object typed at
  the binding's layer, or to a variable of `G'` with the same binding.
  Its objects are deep-normal. **M2 restriction:** a context variable `g`
  is sent only to a context variable (`GId`), never to a concrete context.
  Instantiating `g` needs the tail-expansion argument (`δ` must then send
  the new explicit entries of `σ(g)` to the matching variables). That only
  becomes necessary with `CΠ` (M2b), and validity in M2 only quantifies over
  such `σ`.
- **`gctx` is a primitive record** (definitional eta), so `[⊢ G]` and
  `[⊢ mkG (gL G) (gΨ G)]` are interchangeable.
- The inductive type of global weakenings is called `gweak`, so that it
  doesn't clash with `gwk d`, the local substitution moved under a global
  binder.

## Fork, with the chosen default

**Static-code payload.** The simplified payload (`⊢_C` plus `⊩^{≥P}_P`)
suffices for `letbox`. The paper's inductive `⊩^C_P` record is what the
recursors need. Default: simplified now, behind an interface (constructor
lemmas plus projection to `⊩^{≥P}_P`), so that M3 swaps the definition and
reproves only the interface lemmas and the FT cases that build payloads.
The alternative, the full record now, costs a k = C obligation for every
C-layer rule in the FT right away.

## Status (2026-09-24, session 3)

Steps 1–2 are done: syntax and all of the declarative metatheory. The tree
is green, with no admits and no axioms. A clean build takes about 37 s.

| File | Contents |
|---|---|
| `Syntax/Term.v` | `CTyp`, `CTrm`, `box`, `letbox` constructors; global renaming and substitution (`gobj`, `gup`, `pty/ptm/pctx`, `gsingle`), notations `x⟪ξ⟫`, `x⦃σ⦄` |
| `Syntax/GSubst.v` | global laws (ext, composition with local and global operations, identity on deep-normal input), `dnf*` and its preservation |
| `Syntax/NormalForms.v`, `Reduction.v` | `box` whnf, `letbox` neutral, letbox β on `box`, scrutinee congruence |
| `Typing/Declarative.v` | global bindings, `U^δ`/`u^δ`, `□`, `box`, `letbox`, their congruences and β, `eq_ctx` |
| `Typing/GWeakening.v` | `gweakening` (global weakening, every judgment and layer) |
| `Typing/Lifting.v` | `lifting` (`i ≤ j`) |
| `Typing/Properties.v` | `weakening_all` (local, every layer) |
| `Typing/Substitution.v` | `typed_dnf`; `lsub_wf` record with tails; `substitution_all` |
| `Typing/Functionality.v` | `functionality_all` (every layer) |
| `Typing/GSubstitution.v` | typed global substitutions; `gsubstitution` (context variables to context variables); declared bindings are well formed; single substitutions |
| `Typing/Presupposition.v` | presupposition incl. context equivalence (`eqctx_id`: conversion), letbox β via `gsubstitution` |

**Transition state of the semantics.** M1's logical relation and validity
are unchanged, apart from `SubRel` carrying tails and deep normal forms.
The fundamental theorem and its consequences are restricted to `ge_layer
= lD` and to global contexts with context-variable bindings only
(`ctx_only`), because the new rules live at M or need term/type bindings.
Steps 3–6 lift the restriction.

## Order of work

1. Syntax: new constructors, global renaming/substitution, laws, whnf and
   reduction (letbox β on `box`, congruence in the scrutinee, no reduction
   under `box`).
2. Typing: the new rules at all layers (D2), global context
   well-formedness, C-layer gating; then the metatheory (D3).
3. Generic laws + declarative instances at P and M (D4).
4. Global Kripke refactor of M1's relation (D5), properties re-proved;
   `j` index; `vp`; `□` constructors; the properties' new cases.
5. `⊩^{≥P}_P`, the payload, related global substitutions, Layering
   Restriction.
6. Validity with σ; FT for C/P/M; consequences (□ injectivity; closed
   canonicity for □ at empty Ψ as an extra, not in the paper).

## Paper inconsistencies noted (all read as typos)

- The letbox scrutinee is typed at level `1+l` (04:1108) or `l` (04:1116);
  it should be 0.
- `x_T` is written for `x_t` at 04:1405 and 04:1233.
- `M_Trm` is written for `M_Typ` at 04:1555.
- 05:209 has a `u : DTyp` typo.
- 05:269 has `u/u` where `u^id/u` is meant.
- 7a:44 has `Δ ≈ Δ` where `Δ ≈ Δ'` is meant.
- "`\metalevel`" is used for a length or the number 0 in several places
  (07:83, 07:341, 05:236); it is a macro-rename artefact.
- The generic `□` type-constructor laws use the same level on both sides.
