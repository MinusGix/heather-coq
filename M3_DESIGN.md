# Milestone 3: universe substitutions and the code recursors

Goal: extend M2 with the two recursion principles on code,
`elim_Typ^{l₁,l₂} M⃗ b⃗ l Δ t` and `elim_Trm^{l₁,l₂} M⃗ b⃗ l Δ T t`
(04:816–1250), with their β rules, the neutral-recursion laws, and the
fundamental theorem at M. Their branches are typed under fresh universe
level variables, so M3 first adds universe substitutions `φ` and makes
validity stable under them (07b quantifies every semantic judgment over
`φ ≈ φ' : L' ⇒ L`).

Paper references: 04:800–1000 (syntax, the 4 + 9 branches), 04:1127–1260
(typing: motive group `G_M`, type branches `G_Typ`, term branches
`G_Trm`), 04:1540–1620 (β rules, a selection), 05 (the operations on the
recursors), 06:86–145 (reduction: index first, then scrutinee), 07:371–400
(neutral recursion laws), 07a:118–340 (the `⊩^C_P` record), 07b:1428–1550
(the mutually proved recursion lemmas).

## Scope (user decision, 2026-09-25)

| Stage | Contents |
|---|---|
| **M3** (this doc) | universe renaming/substitution (syntax, laws, typing lemma), validity quantified over `φ`, both code recursors (syntax, schematic β, reduction, typing, metatheory, neutral laws, FT at M) |
| M4 | `UΠ` / `Λ` / `$` and `ω`: the only uses of universe *weakenings* inside the relation (Kripke) |
| M2b | `CΠ`, `TΠ` (unchanged plan; independent of M3) |

## Decisions

### E1. Level variables are de Bruijn indices

`lvar 0` is the most recently bound level (M1 fixed "de Bruijn level
variables" without a binder; M3 introduces the first binders). Indices
make instantiation `l/ℓ` a single substitution that does not need `L`. That
matters because the schematic β reduct (E4) is computed by *untyped*
reduction, which does not know `L`. Cost: a local or global substitution
passing under a level binder is universe-weakened (`uwk`), exactly as a
local substitution passing under a global binder is globally weakened
(`gwk`).

Operations: universe renaming `x⟨ρ⟩ᵤ` (`ρ : nat -> nat`) and universe
substitution `x[φ]ᵤ` (`φ : nat -> lvl`) on `lvl`, `ty`, `tm`, `ctx`,
`lsub`, `gobj`, `gdecl`. Level syntax is traversed by them only. Local and
global operations leave levels alone and never pass under anything but
their own binders, *except* at the new scope marker (E2).

### E2. Branch syntax: single-step binder markers in one bundle

A branch binds `nu` levels, `ng` globals and `nl` locals (e.g. `t_Π`
binds `ℓ, ℓ'; g, U_S, U_T; x_S, x_T`). Junk `tm` constructors, never typed
on their own (like `tmErr`), carry the scoping:
- `bindU b`, `bindG b`, `bindL b` each bind one level, global or local
  variable. Every operation passes under them with its existing
  single-step lift (`uwk`/`gwk`/`llift` for local substitutions,
  `guwk`/`gup` for global ones, `uupr`/`uup`, `gupr`, `rlift`), so the
  existing single-step hint lemmas discharge the new cases.
- `tmTy T` embeds a motive; `tmTup s t` pairs.

A component is wrapped levels outermost, then globals, then locals, in
the paper's binding order. The recursors are `elimT l₁ l₂ rb l Δ t` and
`elimt l₁ l₂ rb l Δ T t`, where the bundle
`rb = mkrb MT Mt bs` (`Syntax/Recursor.v`) nests the two wrapped motives
(`MT` binds `ℓ; g; x_T`, `Mt` binds `ℓ; g, U_T; x_t`) and the 13 wrapped
branches (arity table `br_ar`). The four mutual sorts are unchanged, so
no existing `*_all` law statement changed.

### E3. Typing: the branch group as one premise

The 13 branch premises of `G_A` become one premise: for each branch index
`k`, the branch body is typed in the branch's global context, local
context and motive instance (`brG k`, `brΓ k`, `brT k`, computed from the
arity table and the motives). This is strictly positive, and the scheme
gives the functional IH, as for local-substitution typing (M2 D2). Every
metatheory lemma then has one branch case, discharged by per-branch
commutation lemmas for `brG`/`brΓ`/`brT` (13 cases, proved once per
operation).

### E4. β rules: one schematic rule per recursor (user decision, 2026-09-25)

The paper states a few of the 13 β rules and says the rest follow the same
pattern. We state one rule per recursor: `elim_Typ … (box c) ≅ ρ` whenever
`redT … c = Some ρ`, and likewise for terms with the index's whnf. The
reduct functions `redT`/`redt` compute `t_k[levels][Δ/g, subcodes][rec
calls]` by case on the head of `c` (and, for `λ` and variables, on the
whnf of the index `T`). They return `None` on global-variable heads
(neutral: 07:371). The premise is the typing of the left-hand side; the
paper's 13 rules are derived lemmas. Reduction uses the same functions.

Reduction order (small deviation from 06:136–145, which reduces the index
of `elim_Trm` first and calls the order arbitrary): the index is reduced
only when the scrutinee is a boxed `λ`, the one head whose reduct reads
it. So `whne` does not mention types (a recursor is neutral when its
scrutinee is neutral or a boxed global variable), and reduction stays
deterministic. `red` and `red_ty` become mutually inductive (`red_both`).

### E5. The `⊩^C_P` record is syntactic; its semantics comes from the FT at P

The paper's record (07a:118–340) stores, at every node of the code, the
structure *and* `⊩^{≥P}_P` of the subterm. In our development the
fundamental theorem at P (`fundamentalS`) is already proved for *all*
derivations, and neither code nor P-derivations contain recursors. So the
semantic half is recoverable at any node from C-typing: lift to P, apply
`fundamentalS`, instantiate at the identities (`Reducible`). Consequences:
- the `□` relation, its payload (`vp_tyc`/`vp_tmc`: literal equality,
  C-typing, `⊩^{≥P}_P`) and related global substitutions are **unchanged**
  (M2_DESIGN's "payload becomes simple ∧ record" upgrade is unnecessary);
- the record is a syntax-directed inversion of C-typing (conversion folded
  into each node, as in the paper), proved from C-typing by induction on
  the derivation, and it is the induction measure of the recursion lemmas
  (07b:1428).

### E6. Validity is stable under universe substitutions

As in 07b, the FT's motives quantify over `φ : L' ⇒ L`:
`V^φ(J) := ∀ L' φ, φ : L' ⇒ gL G → V(J[φ])` with M2's validity `V` at the
substituted judgment. Every existing FT case is the M2 case at the
φ-instance (typing premises pushed through the syntactic universe
substitution lemma). No relation-level stability under `φ` is needed. The
recursor case needs `∀φ` for the branch premises, which are typed under
`L + nu` and instantiated at `(φ, levels of the code)`.

### E7. Branch contexts: a context premise, prefix-wise weakening and substitution

A branch is typed in a context extended by the types of its recursive
calls (motive instances). Local weakening and local substitution cannot
rebuild that extended context from their induction hypotheses, since the
entries' derivations are not premises. So the recursor rules carry the
branch contexts' well-formedness as a premise
(`[brG k G ; brΓ k Γ … ⊢M]`, redundant as in logrel-coq-style rules), and
the context motives of local weakening and local substitution are
prefix-wise: for `Θ = cexts Γ As`, weakening/substituting `Γ` lifts through
`As` (`cexts_ren`, `cexts_sub`). Universe substitution and global
weakening already have context motives that absorb it.

Operations commute with peeling only on terms not headed by a (global)
variable (`hd_ok`); the bundles built by `mkrb`/`wrapMT`/`wrapMt` satisfy
this by computation, and a typed recursor's bundle is literally
`mkrb MT Mt bs` (`elimT_rb_shape`).

### E8. Functionality with a prefix-wise context motive

Functionality of a recursor needs its branch contexts' entries (motive
instances) related under `d` and `d'`. The context motive of functionality
is prefix-wise and yields the lifted equal substitutions directly: from
`Δ ⊢ d ≅ d' : Γ` it gives
`cexts Δ As[d] ⊢ lliftⁿ d ≅ lliftⁿ d' : cexts Γ As`, the entries'
equalities coming from the type induction hypotheses of the branch-context
premise (E7). No global substitution is needed, so the metatheory order
is unchanged.

### E9. Global substitution of context variables by concrete contexts (user decision, 2026-09-25: inside M3)

The recursor's result type `M_Typ[l/ℓ, Δ/g, t/x_T]`, its β reducts, and
the branch scopes' instances `(g, x : U_S^id)/g` instantiate a context
variable with a concrete context. M2 restricted the global substitution
lemma to context variables ↦ context variables (deferred to M2b's `CΠ`);
M3 lifts the restriction ("tail expansion": a context ending in `g`
becomes the entries followed by the image, lengths and the tail
condition of typed local substitutions shift accordingly), in the
syntactic lemma and in related global substitutions (a context variable
goes to related contexts, as in 07a), since the recursor FT instantiates
branch validity at `σ, Δ/g, …`.

### E10. Recursor rules carry their presuppositions (logrel-coq style)

Three premises are added to the recursor rules, each admissible in the
paper's system:
- `wf_elimT`/`wf_elimt`: the result type (the motive instance
  `motT (wrapMT MT) l Δ t`, resp. `mott`) is well formed;
- `eqtm_elimT`/`eqtm_elimt`: the two motive instances are equal;
- `eqtm_elimT_beta`/`eqtm_elimt_beta`: the reduct is typed.

Why: functionality has no induction hypothesis for equations, so it
needs the instance's typing to relate its two substitution instances, and
the instance lemma (`RecInst`: universe, then global with `g ↦ Δ`, then
local substitution) comes after global substitution, which uses
functionality. The instance equation of a congruence would need
functionality of universe substitution in equivalent levels and of global
substitution in convertible contexts (the latter after context
conversion). The reduct's typing (subject reduction for the 13 heads) is
needed only by presupposition: typed reductions carry their equations
(logrel-coq), and the recursion lemma gets the reduct's typing by escape
from its reducibility. Every metatheory lemma transports the new premises
through its induction hypotheses (the `regty` step up to the operation's
`motT`/`mott` law); `RecInst` builds them when a recursor is constructed
from scratch.

### E6'. Equivalent level instantiations: a level-invariant relation (user decision, 2026-09-25)

E6 as first stated (validity at one `φ`) is too weak on its own for the
recursion lemmas, which relate two *equivalent* level instantiations:
- the congruence `elim_Trm … l …  ≅ elim_Trm … l' …` with `l ≡ l'`: the
  variable branch is instantiated at `ℓ := l` on one side and `ℓ := l'` on
  the other;
- the `Π` β step: the recursor's type is `M_Typ[l/ℓ, …]` with the index
  level `l`, the reduct's is `M_Typ[l₁ ⊔ l₂/ℓ, …]` with the code's levels,
  and `l ≡ l₁ ⊔ l₂` only up to equivalence (level conversion in the code's
  typing); likewise the codes of a related pair of boxes are only
  `≡ₗ`-related (E11).
First decided: validity two-sided in `φ ≈ φ'` (as 07b:1428). Revised after
costing (user decision): keep the one-sided FT (`fundamentalM_us`) and add
**level invariance of the relation**: the relation is unchanged when
well-typed syntax is replaced by `≡ₗ`-related well-typed syntax. It uses
the Static Code Lemma at every layer (declarative equality of typed
`≡ₗ`-related syntax) and a generic law saying the generic relations
respect `≡ₗ` (declaratively: static code and transitivity).
Implemented as: `LevelRed.v` (reduction simulates across `≡ₗ`; the
weak-head normal forms of related syntax are related), generic laws
`g{ne,eq}_{ty,tm}_leq` in diagonal form (each side related to itself),
`VParam` laws `vpl_*_leq`, and `LevelInv.LR_leq`: `LR T1 T2 R`,
`LR T3 T3 R3`, `T2 ≡ₗ T3` give `LR T1 T3 R` and `R t1 t2 → R3 t3 t3 →
t2 ≡ₗ t3 → R t1 t3` (induction as for transitivity; the `□` cases by a
diagonal bridge composed with `ModRel_trans`). Lifted to validity in
`CtxRel.v` (`VTy(G)_leq`, `VTm(G)_leq`, `CtxRel(G)_leq`).

### E11. Boxed code is compared up to level equivalence (user decision, 2026-09-25; revises M2 D3)

M2 made `box` congruence literal (`box c ≅ box c` only). That makes
`J[φ] ≅ J[φ']` false as soon as `J` mentions a level variable inside boxed
code (`box (Ty ℓ)` at `ℓ := lzero` and `ℓ := lzero ⊔ lzero`), and with it
the `Π` β step above. The paper's Static Code Lemma (05:1055) compares
C-level code up to level equivalence, and we now follow it:
- a syntactic relation `≡ₗ` (same shape, level annotations equal under
  every valuation), closed under all syntactic operations;
- `box` congruences `box T ≅ box T'` for C-typed `T ≡ₗ T'`
  (`eqtm_boxT`/`eqtm_boxt` return, with `≡ₗ` in place of C-equality); the
  generic `box` laws, the `□` payload and the C/V images of related global
  substitutions compare code by `≡ₗ`;
- the static-code lemma becomes `T⦃σ⦄ ≡ₗ T⦃σ'⦄` for substitutions whose
  static images agree up to `≡ₗ`, still a syntactic induction (the reason
  M2 retired the C-equality congruence does not apply to `≡ₗ`).

### E12. Level equivalence at M is a rule (user decision, 2026-09-25)

E6' needs, at every layer, that well-typed `≡ₗ`-related syntax is
declaratively equal. Below M this is the Static Code Lemma
(`StaticCode.static_code`, by induction on the left derivation). At M we
take it as a rule instead: `eqty_leq`/`eqtm_leq` (layer `lM` only, both
sides typed at the same type and level). Proving it at M would need two
lemmas used nowhere else: global-context conversion for `letbox` bodies
(`gext G (gdTy Δ …)` to `gext G (gdTy Δ' …)`) and branch-context
conversion for the recursors (`brΓ k` with `MT` to `brΓ k` with `MT'`,
13 shapes). The rule is admissible and its validity case is exactly the
relation's level invariance, which E6' proves anyway. Deviation from the
paper: the declarative system has one more (admissible) rule at M. Each
typing induction has one more case, closed by the `≡ₗ` closure lemmas
of `LevelEq.v`.

### E13. The recursion lemmas: architecture

The FT case for `elim_Typ` (congruence form; typing is the reflexive
instance, β follows by anti-reduction) unfolds validity to: related
global substitutions `σ ≈ σ'` into `G[φ]`, related local ones `e ≈ e'`
into `Γ[φ]⦃σ⦄`, and a scrutinee whose whnfs are either related neutrals
or `box c`, `box c'` with `c ≡ₗ c'` C-typed in `Δ⦃σ⦄` (the payload).
- **Recursion lemmas** (`rec_T`, `rec_t`, mutual): by induction on the
  C-typing derivation of `c` *at the target* `G'` (E5: no semantic
  record), for all related contexts `Δ ≈ Δ'` (P, both instances, and
  declaratively) and `c' ≡ₗ c`, `elimT … (box c)` and `elimT' … (box c')`
  are related at the motive instances. `rec_t` quantifies over index
  types convertible to the derivation's type (the conversion case, and
  the `λ` case, which reads the index's whnf).
- **A β reduct is a substitution instance of its branch**: peeling a
  wrapped branch with level, global and local lists is the triple
  substitution by `ulist`/`glist`/`llist` (`peel_wrap`). The branch's
  validity (the FT's `∀ψ` induction hypothesis) is instantiated at
  `ψ = levels(c) ++ φ`, at `σ` extended by the code's pieces (`GCtx Δ`,
  `GTy A`, …), and at `e` extended by the recursive calls (related by the
  recursion hypotheses). Left and right codes have `≡ₗ`-related levels:
  both reducts are instantiated at the left levels, then the right one is
  switched back by level invariance (E6').
- **Images are related from syntax**: a pair of well-typed images at a
  static declaration (`≡ₗ`-related at C, declaratively equal at P/V,
  contexts declaratively equal) is `GObjRel`-related, by the FT at P at
  the identity instance and `VTyG_leq`. This builds the extensions of
  `σ` by code pieces, and the universe weakening `GSubRel_uwk` that the
  neutral case needs (the branches are compared under their `nu` level
  binders at `ψ = uupn nu φ`); the relation itself is never universe
  weakened (M4).
- **Neutral scrutinees** (neutral, or a boxed global variable): the
  neutral recursion laws, whose `ElimPrem` comes from the motives' and
  branches' validity at the identity extension of `σ` (escape).
- **Typed reductions**: the reduct's typing comes by escape from its
  reducibility (E10).

### E14. Universe weakening of the relation (user decision, 2026-09-25: inside M3)

The neutral recursion laws need the motives and branches generically
equal under their binders (`ElimPrem`), at `recGT G'` / `recΓT Θ` and
the branch scopes. There the ambient M-context is universe weakened
(`uwk`), so escaping from the motives' validity needs the related local
substitution `e` to stay related after `uwk`: the relation must be stable
under universe weakening. (The earlier plan kept this for M4's `UΠ`.)

Rather than adding universe renamings to the Kripke worlds, which would
make `VTyG` and every FT case work at renamed worlds, the stability is
assembled from two cheaper facts:
- **Level growth is a world.** `gwk_ok γ G' G` allows `gL G ≤ gL G'`
  (fresh levels at the top; existing syntax is untouched). Annotations
  quantified in the base world shrink back: a level equivalent to a
  well-formed one mentions only its variables (occurrence lemma).
- **Permutations.** A bijection `π` of level variables that fixes
  everything from `gL G` up preserves the relation (`LR_perm`), with the
  term relation transported explicitly
  (`dnf t ∧ dnf t' ∧ R t⦅π⁻¹⦆ t'⦅π⁻¹⦆`, no choice). Π's Kripke worlds are
  pulled back along `π⁻¹`; `URel`'s annotations are pulled back
  syntactically.
- `uwk` is growth by one followed by the rotation that sends the new top
  level to `0`. On syntax scoped below `gL G` (every typed object:
  scoping lemma) the rotation acts as `ush 1`.

The generic laws gain stability of `~`/`≈` under universe substitutions
(declaratively: the universe substitution lemma), and `VPLaws` gains the
same for the parameters.

## Order of work

1. **Syntax** (done). Level renaming and substitution; the bundle nodes,
   `elimT`, `elimt`; every existing operation extended; universe
   operations on all sorts; laws (the existing ones for the new
   constructors, plus the universe laws and their commutation with the
   local and global operations); normal forms; the reduct functions;
   reduction.
2. **Typing.** Universe weakening/substitution on contexts and `gctx`;
   the recursor rules (typing, congruence, schematic β) at M; the
   metatheory cascade (global weakening, lifting, local weakening,
   substitution, functionality, global substitution, presupposition),
   plus the **universe substitution lemma**.
3. **Generic laws.** Neutral recursion (07:371–400) at M, reflexive in
   the `box`-of-global-variable form; declarative instance.
4. **Relation and validity.** `whne` gains the neutral recursors (the
   relation needs no new case: the recursors are eliminators). Validity
   and the FTs gain the `∀φ` quantifier.
5. **Record and recursion lemmas.** The code-structure record, C-typing ⇒
   record, and the two mutual recursion lemmas by induction on it.
6. **FT cases** for the recursors at M (congruence, β), then the
   consequences at M again (whnf, canonicity).
