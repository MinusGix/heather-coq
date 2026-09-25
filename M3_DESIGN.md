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

### E2. Branch syntax: a scope marker and a pairing node

A branch binds `nu` levels, `ng` globals and `nl` locals (e.g. `t_Π`
binds `ℓ, ℓ'; g, U_S, U_T; x_S, x_T`). Two junk-sorted `tm` constructors,
never typed on their own (like `tmErr`):
- `tmBind nu ng nl b` marks `b`'s scope. Every operation passes under it
  generically: `ren` by `rlift^nl`, local substitution by
  `llift^nl ∘ gwk^ng ∘ uwk^nu`, global renaming by `gupr^ng`, global
  substitution by `gup^ng` of the universe-weakened images, universe
  operations by their `nu`-fold lift.
- `tmTup s t` pairs; the branch bundle is a fixed-shape nest of 13
  `tmBind`s.

The four mutual sorts stay as they are, so no existing `*_all` law
statement changes; the new cases are handled by `law_auto` once the
iterated-lift hint lemmas exist.

The recursors are
`elimT l₁ l₂ MT Mt bs l Δ t` and `elimt l₁ l₂ MT Mt bs l Δ T t`,
where `MT` binds `ℓ; g; x_T` and `Mt` binds `ℓ; g, U_T; x_t` (fixed
arities, handled in the recursor cases directly).

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
paper's 13 rules are derived lemmas. Reduction uses the same functions;
it reduces the index of `elim_Trm` to whnf first, then the scrutinee
(06:136–145).

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

## Order of work

1. **Syntax.** Level renaming and substitution; `tmBind`, `tmTup`,
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
