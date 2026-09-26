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

Status: **in progress.**

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

Status: planned.

## B. Generalizations and packaging

### B1. Closed canonicity at every type former

Today: `Nat`, `□Ty`, `□Tm`. General form, for `ctx_only G` and the empty
local context:
- a well-typed term reduces to a non-neutral whnf. By the type, that
  whnf is a numeral constructor, `λ`, a code, `Λ`, a context or type
  abstraction, or `box`;
- a well-formed type reduces to a non-neutral type former.

From `no_closed_neutral`, normalization and head discrimination.

Status: planned.

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

A1, A3, B1, A2, then B2. The C items are designed separately when
reached.
