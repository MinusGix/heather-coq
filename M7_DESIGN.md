# Milestone 7: strengthening the base

Goal: before the user's extensions, fill the gaps between the paper and the
formalization, and add consequences that generalize or package what M1–M6
proved. No new syntax or rules.

Items are grouped by kind. Each has a status, the paper reference where
there is one, and the sketch it was scheduled with. Record decisions and
deviations here as items land.

## A. Paper results not yet formalized

### A1. Consistency (08:48)

Paper: no `t` with `· ; · ; ℓ ⊢_M t : Π^{1+ℓ,ℓ} (x : Ty ℓ). x @ 1+ℓ`.

Planned generalization: any global context of context variables only
(`ctx_only G`), any level context, any well-formed level `l`, at D and M.

Sketch:
- Apply `t` to a fresh variable, giving a term of `El l (var 0)` in
  `x : Ty l`.
- Its whnf is neutral: the type is neutral, and no closed-style value
  inhabits it.
- Every neutral in `x : Ty l` (with `ctx_only G`) infers a type equal to
  `Ty l`: its head can only be `var 0`, and every eliminator needs a head
  of a type other than `Ty l`.
- `El l (var 0) ≅ Ty l` is then a head clash.

Status: **done** (`Validity/Consistency.v`), closed under the global
context. As built:
- `univ_ctx Γ`: every local entry is a universe. `ctx_only G`: every
  global entry is a context variable.
- `neutral_univ`: in such contexts, a typed neutral has a type equal to a
  universe. Induction on `whne` with the typing inversion lemmas:
  - a local variable has a universe type;
  - a global variable, or a recursor over a boxed one, contradicts
    `ctx_only`;
  - each eliminator's scrutinee type (`Nat`, `Π`, `□`, `UΠ`, `CΠ`, `TΠ`)
    clashes with a universe by head (`decl_head_c`).
- `no_type_var_inhabitant`: no term of `El l (var n)`. Completeness gives
  an algorithmic derivation. At the neutral type `El l (var n)` only the
  neutral rule applies, so the whnf is neutral, and `neutral_univ` gives
  `El l (var n) ≅ Ty l'`, a head clash. The algorithm replaces the
  paper's argument through the relation at a neutral type.
- `consistency`: no term of `Π^{l1,l2} (x : Ty l). El l' x` in any such
  context. The η body `t x` would inhabit a type variable.
  `consistency_closed` is the paper's statement: the empty local context.
  It holds at any levels and any global context of context variables, at
  D and M.

### A2. Soundness of plain reduction and preservation (06:148, 06:264)

M1 deviated: typed reduction carries its equation (`Typing/TypedRed.v`),
because β needs Π-injectivity, which only the logical relation gives. It
is available now (M1–M5 consequences).

Statements:
- `[t : T]` and `t ⤳ t'` give `[t ≅ t' : T]` and `[t' : T]`, and the same
  for types, at every layer (V has no reductions; C lifts to D).
- The multi-step forms.

This closes the deviation. The recursor β-steps are the bulk; the
typed-reduction lemmas the logical relation uses likely cover them.

Status: planned.

### A3. Static Code, the paper's direction (05:1055)

At V and C, declarative equality implies `≡ₗ`. `StaticCode.static_code`
has only the converse. Consequences:
- at V/C, equality is exactly typed `≡ₗ`;
- the `≡ₗ` premise of `eqtm_boxT`/`eqtm_boxt` is admissible, so the
  paper's `box` congruence is a derived rule;
- decidability of declarative equality at all four layers (V/C via
  `leq_dec_all`, D/M via M6).

A syntactic mutual induction; the global-variable case needs the
substitution entries (`telescope`-style).

Status: **done** (`Typing/StaticCodeEq.v`), closed under the global
context. As built:
- `static_code_eq`: at `lle i lC`, equal types, terms and local contexts
  are `≡ₗ`-related. The proof is an induction on `typing_mut`:
  - the computing (`compt i`) and M-only rules are vacuous;
  - the congruences map `lequiv` to `leqv` (`lequiv_leqv`);
  - PER and conversion rules are immediate;
  - global variables compare their substitutions entrywise.
    `l_canon_leq`, the `≡ₗ` form of `l_canon`, says normal substitutions
    are `≡ₗ` iff their lookups are. `lsub_leq_entries` covers the entries
    past `Δ` using `lsub_tail`.
- `static_code_iff_ty`/`_tm`: with the converse (`static_code_ty`/`_tm`),
  equality of typed syntax at V and C is exactly `≡ₗ`.
- `decl_eqty_dec_static`/`_tm`, and in `Validity/AlgDec.v`
  `decl_eqty_dec_any`/`decl_eqtm_dec_any`: declarative equality of typed
  syntax is decidable at every layer.
- `eqtm_boxT'`/`eqtm_boxt'`: the paper's `box` congruence (06:534),
  without the `≡ₗ` premise that `eqtm_boxT`/`eqtm_boxt` carry (M3 E11).
  That premise is now shown admissible.

## B. Generalizations and packaging

### B1. Closed canonicity at every type former

Today: `Nat`, `□Ty`, `□Tm`. General form, for `ctx_only G` and the empty
local context:
- a well-typed term reduces to a non-neutral whnf. By the type, that
  whnf is a numeral constructor, `λ`, a code, `Λ`, a context or type
  abstraction, or `box`;
- a well-formed type reduces to a non-neutral type former.

From `no_closed_neutral`, normalization and head discrimination.

Status: **done** (`Validity/Canonicity.v`), closed. As built, at D and M
with `ctx_only G`:
- `closed_type_canonicity`: a closed type reduces to a whnf that is not
  neutral. A type variable would need a `gdTy` declaration, and `El` of
  a closed neutral contradicts `no_closed_neutral`.
- `closed_canonicity`: a closed term reduces to a non-neutral whnf `w`,
  its type to a whnf `W`, and `canon_head (ty_head W) w`. The value's shape
  is indexed by the type's head:
  - `zero`/`succ` at `Nat`;
  - a code (`tmNat`, `tmU`, `tmPi`) at a universe;
  - `lam` at `Π`, `boxT`/`boxt` at `□`, `ulam` at `UΠ`, `clam` at `CΠ`,
    `tlam` at `TΠ`.
- `value_canon`: a typed value's shape matches its whnf type's head. Each
  value's typing inversion ends in an equation with its canonical type
  former; `decl_head_c` compares heads.
- `closed_canonicity_whnf` (type already whnf) and `closed_pi_canonicity`
  (closed functions compute to `λ`) as examples of use.

### B2. Uniform statements

- `compt i` forms of the `decl_*`/`declM_*` pairs (normalization,
  injectivity, discrimination).
- `decl_eqty_dec` with the two sides at possibly different levels.
- `decl ↔ ac` as one iff per judgment.

Status: planned.

## C. Ambitious

### C1. Decidability of type checking

A bidirectional checker for the annotated syntax, with decidability of
`[G; Γ ⊢[i] t : T @ l]` (and well-formedness of types, contexts, global
contexts) for the computing layers. Uses M6 for conversion, injectivity
for inversion, and normalization to expose type heads. The level
annotations may make inference mostly syntax-directed. Open questions:
- which annotations the syntax lacks (e.g. `box`'s local context);
- the recursor bundles.

Status: to design.

### C2. Deep normalization

Normal forms (not only weak-head), and every typed term equal to one;
uniqueness up to `≡ₗ`. Candidate route: read normal forms off the
algorithmic derivations of M6, or a normalization-by-evaluation instance
of the generic equivalence.

Status: to design.

### C3. Faithfulness to the paper's rule set

A theorem that our system derives exactly the paper's judgments:
- the explicit reflexivity rules and the extra well-formedness premises on
  congruences (M1 deviation) are admissible;
- `eqty_leq`/`eqtm_leq` at M (M3 E12) are admissible.

Status: to design.

### C4. An executable checker

A fuel-based, `Type`-valued decision procedure for conversion (M6 H1)
and, with C1, type checking, as in logrel-coq.

Status: to design.

## Order

A1, A3, B1 (done); A2, then B2. The C items are designed separately when
reached.
