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

Status: **done**, closed. The final statements, unconditional, are in
`Validity/RecReduct.v`: `reduction_sound_tm`/`_ty`,
`subject_reduction_tm`/`_ty`, `reductions_sound_tm`/`_ty` (at D and M).
The M1 deviation (typed reduction carrying its equation) is now a design
choice only: the paper's statements hold for plain reduction.
- A2a: `red_sound_all`, and the consequences `red_sound_tm`/`_ty`,
  `preservation_tm`/`_ty`, `reds_sound_tm`/`_ty`, at D and M, premised on
  `RecRedTyped` (a recursor's β-reduct is typed at the redex's type).
  Each redex is inverted. The β rule applies at the inverted
  annotations, and congruence moves back to the redex's, using:
  - `pi_inj_c`, `declM_upi_inj`/`cpi_inj`/`tpi_inj`,
    `declM_CTyp_inj`/`CTrm_inj`;
  - instance equations under the universe (`uinst_eqty`) and global
    (`inst_eqty`) substitutions.
  The recursor congruences use `motT_eq_scrut`/`mott_eq_scrut`. The
  index step under a boxed `λ` uses `declM_mott_eq` (functionality, a
  consequence of the FT); the semantic proof took that equation as a
  premise.
- A2b: discharge `RecRedTyped`. The semantic proof (`RecS`) obtains a
  reduct's typing from branch validity. Syntactically, a reduct is its
  branch body at extended substitutions (`RecPeel`). Its typing is the
  branch's typing (`brG k`/`brΓ k` at `brRes k`) under:
  - the universe substitution by the code's levels;
  - the global substitution by the code's pieces, typed from the code's
    C-typing inversion;
  - the local substitution by the recursive calls, typed by the recursor
    rule at the sub-codes.
  Then the instance equation with `motT`/`mott`, for each of the 13
  code shapes.

  As built (`Validity/RecReduct.v`):
  - `br_typed`: a branch body is typed at typed extensions, via
    `usubstitution`, `gsubstitution` and `substitution`. The extensions are
    built one binding at a time (`gsub_wf_snoc`, `lsub_wf_lcons`). The
    reduct's peel form becomes the triple substitution by
    `RecPeel.peel_wrap`, and the instances are identified by
    `motT_wkb_inst'`/`mott_wkb_inst'` with `motive_id_T`/`_t` (identity
    substitutions on the motives).
  - Type codes (`rr_T_nat`, `_pi`, `_U`, `_El`) invert the code's
    C-typing, and `rr_T_all` moves to the redex's level (`motT_move`, by
    `declM_motT_eq`).
  - Term codes are shape lemmas at the natural instance (`rr_t_var`,
    `_nat`, `_U`, `_zero`, `_succ`, `_pi`, `_natrec`, `_lam`, `_app`).
    `rec_t_code` is an induction on the code's C-typing: the inversion
    lemmas need `typeof i = i`, which fails at C. Its motive (`RTC`)
    quantifies over the redex's index and level, equal to the code's type
    and level, because the `λ` reduct reads the index's codomain
    syntactically. Conversions of the code's typing are absorbed
    (`C_conv`, `C_lconv`), and `mott_move` (by `declM_mott_eq`) moves to
    the redex's instance.
  - No induction on the recursion is needed: the recursive calls are
    typed by the recursor rule at the sub-codes (`recT_wf`, `rect_wf`).
  - Gotcha: after `cbn`, substitutions appear in raw form (`subst_ty`,
    `gcsubst`) while the lemmas use the class notations. `sl0`/`sl0t`
    cover both forms, and the target contexts are restated by `change`
    rather than computed.
- At C: lifting to D and unlifting (05:1039) would transfer the result;
  not yet stated.

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

Status: **done** (`Validity/Uniform.v`), closed:
- `whnf_normalization_ty_c`/`_tm_c`, with the equation (the term form
  via soundness of reduction, A2);
- `closed_nat_canonicity_c`;
- `ac_ty_iff`/`ac_tm_iff`;
- `decl_eqty_dec_lv`: the sides at possibly different levels. Equal
  types are well formed at the judgment's level, and levels of a type are
  unique up to equivalence (`ty_lvl_uniq`).

Injectivity of `Π` and `U` and head discrimination already had `compt i`
forms (`pi_inj_c`, `U_inj_c`, `decl_head_c`); the other type formers are
M-only.

## C. Ambitious

### C1. Decidability of type checking

Decidability (in `Prop`, as M6 H1) of every judgment's well-formedness
half at every layer V, C, D, M: `[⊢ G]`, `[G; Γ ⊢[i]]`, `[G; Γ ⊢[i] T @ l]`
and `[G; Γ ⊢[i] t : T @ l]`, for syntax in the *redex-free fragment* (J1).
The paper states it (08:236) without proof.

#### J1. The fragment (user decision)

`uapp t ls`, `capp t Δ` and `tapp t A` do not record their function's
body type, so a checker infers it from `t`. When `t` is itself the
matching abstraction (`uapp (ulam …)`, `capp (clam …)`, `tapp (tlam …)`),
the body is only checked, and the redex's type is not determined by its
parts: checking it would invert a substitution (e.g. `ulam 1 l (boxT (Ty
ℓ₀))` applied to `l₀`). The theorem is stated for syntax with no such
redex anywhere (`nlr`), which contains every normal form. Annotating the
three applications (as `app` carries `A`, `B`) or another way of covering
all terms is a future goal (C1b).

#### J2. Shape

Induction on the size of the syntax (so that the branches inside a
recursor bundle and the entries of a local substitution are reachable).
Terms split by whether their type is determined by their syntax:
- *synthesizing*: everything but `lam`, `boxT`, `boxt`, `ulam`, `clam`,
  `tlam`. Annotations or the contexts fix the type: typability is decided
  from the premises (typed at annotated types, checked first), and a
  failure is refuted by inversion. *Uniqueness*: two types of a
  synthesizing term are equal, their levels equivalent. Checking against a
  given type is then M6 conversion (`decl_eqty_dec_lv`).
- *checked*: the given type is normalized to whnf; its head must be the
  construct's former (head discrimination otherwise refutes), whose
  components give the body's type. Needs injectivity of `UΠ`, `CΠ`, `TΠ`,
  `□Typ`, `□Trm` (via the algorithm: completeness, inversion, soundness).
- the heads of `uapp`/`capp`/`tapp` are synthesizing (a checked head of
  the wrong former is untypable by head discrimination; the matching one
  is excluded by J1).

Preconditions inside the induction: the context well formed at
`typeof i`, and for checking, the given type well formed at `typeof i`.
Unconditional statements follow: an ill-formed type or context refutes by
presupposition.

#### J3. Parts

1. Inversion at every layer (conclusions at `typeof i`), presupposition at
   V and C via lifting.
2. Decidable side conditions: context and global lookups, `lsub_tail`,
   `dnfl`, the bundle's shape (`mkrb`), level well-formedness.
3. Admissibility of the recursor rules' scope premises: the branch
   contexts and branch types are well formed when the motives are (also
   C3's).
4. Injectivity of the M formers; uniqueness of synthesized types.
5. The decision procedure.

Status: done, closed. As built:
- `Typing/InvAny.v`: inversion for the heads typed below M, with the
  equation at `typeof i` (`inva_*`); presupposition at V and C by lifting;
  `typed_m_only`, `no_junk` (bundle nodes are never typed), `no_ty_V`.
- `Typing/RecAdm.v` (J3.3): the branch contexts and types are well formed
  from the motives (`brΓ_wf`, `brRes_wf`), hence the recursor rules in the
  paper's form (`wf_elimT_adm`, `wf_elimt_adm`). The motives are moved into
  a branch scope by universe weakening under their binder, global
  weakening past the branch's declarations and `motT_wf`; the scrutinees
  (codes over the branch's variables) are typed by an extension of RecWf's
  `wfd` with the term codes.
- `Typing/DecSide.v` (J3.2): lookups, `lsub_tail`, `dnfl`, the bundle's
  shape (an extraction `unrb` inverse to `mkrb`, `rb_view`), the fragment
  `nlr`, and the size `sz`.
- `Validity/TyInj.v`: J3.4's injectivity, corollaries of `declM_*_inj`.
- `Validity/TypeUniq.v`: `type_uniq`, uniqueness of synthesized types and
  levels (`lvl_eq`), by induction on the term; a checked function's type
  has another former's head (`chk_at_whnf`).
- `Validity/TCBase.v`, `TCType.v`, `TCSynth.v`, `TCCheck.v`: the four
  problems (`TYD`, `CKD`, `SYD`, `CXD`) and one lemma per head, under the
  hypothesis for smaller syntax (`IHsz`). Local substitutions are decided
  as a telescope (`sub_dec`): an entry's type is well formed once the
  later entries are typed. Checking an abstraction or `box` normalizes the
  expected type and reads its head through views (`pi_view` and so on).
- `Validity/TypeCheck.v`: the induction (`sz_all`) and the unconditional
  statements `wf_glob_dec`, `wf_ctx_dec`, `wf_ty_dec`, `wf_tm_dec`,
  `infer_dec`, for `nlr` syntax (`nlr_gctx` for the global context).

Gotchas: several existing lemmas take their typing premise second, after
a side condition that the typing determines (`typed_m_only` now takes the
typing first); the elaboration order of `ltac:`/`I` arguments bit again.
`repeat split` also splits `lequiv` (a conjunction of evaluations), so
build conjunctions explicitly.

#### C1b. Beyond the fragment (future)

Cover the three redex shapes: annotate `uapp`/`capp`/`tapp` with the
body type (a syntax change through the whole development), or decide the
inverse-substitution problem, or another route.

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

A1, A3, B1, A2, B2, C1 (fragment, J1): done. Next: C1b, C2–C4, each
designed when reached.
