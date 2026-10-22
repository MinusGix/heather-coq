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
- the `≡ₗ` premise of `eqtm_boxT`/`eqtm_boxt` (M3 E11) is admissible. It
  was first packaged as primed rules; C3 K2 then removed the premise, so
  the rules are the paper's `box` congruence (06:534).

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
and `[G; Γ ⊢[i] t : T @ l]`. First built for the *redex-free fragment*
(J1), then for all terms once the abstractions were annotated (C1b). The
paper states it (08:236) without proof.

#### J1. The fragment (user decision; superseded by C1b)

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

#### C1b. All terms: annotated abstractions (user decision: route 1)

The abstractions carry the type former they introduce:
`ulam n l T t : UΠ n l T`, `clam l T t : CΠ l T`,
`tlam Δ l l' T t : TΠ Δ l l' T` (scopes as the formers': `T` under the
`n` levels, resp. the new global). Then every redex's head synthesizes,
and J1's exclusion goes away: type checking is decidable for all terms.
Only `box` and `lam`s whose body is checked stay checked-only.

Chosen over annotating the applications (`uapp t n l T ls`, …):
- neutrals are unchanged, so the algorithm's neutral comparison (M6) is
  untouched; abstractions at `UΠ`/`CΠ`/`TΠ` are compared by η, so their
  annotations are never compared;
- fewer mentions (27 files against 34).

Rules: the typing rules read `T` (and `Δ`) off the term, premises
unchanged. Congruences get annotation premises, as `app`'s: `T ≅ T'`
(and `Δ ≅ Δ'`) in the binder's scope. β rules as before; η rules take the
annotation from the type. Reduction and whnfs carry the fields along.

Deviation from the paper (whose `ULAM` is unannotated), recorded in
M1_DESIGN.md. The rules are the paper's with the body type (and `TΠ`'s
context) that a derivation chooses written into the term, so a paper term
is typed iff some annotation of it is. The old syntax is gone, so this is
by construction, not a formal theorem (a formal one would need the
unannotated system alongside: future, if wanted).

Rejected routes, recorded: deciding the unannotated judgment directly
(anti-substitution of levels, context and type variables up to
conversion, principal types of checked bodies; needs C2; research-level;
`tapp (tlam …)` has the variable's context nowhere); reducing redexes
first (unsound: a redex can be untypable while its reduct is typed).

Status: done, closed. `wf_glob_dec`, `wf_ctx_dec`, `wf_ty_dec`,
`wf_tm_dec` (TypeCheck.v) now have no hypotheses; `infer_dec` for every
synthesizing term, which now includes the abstractions. As built:
- Syntax and every operation carry the annotation as the former does
  (`T` under the same binders as the body; `Δ` in the outer scope).
- Rules: typing reads the annotation; congruences `eqtm_ulam`/`clam`/`tlam`
  take `T ≅ T'` (and, for `tlam`, `Δ ≅ Δ'`, and the right body typed at its
  own binder, as `eqty_tpi`); β and η carry the annotation.
- Metatheory: mostly mechanical (patterns with one more field, one more
  induction hypothesis in functionality). Presupposition helpers
  (`pre_ulam_r`, `pre_clam_r`, `pre_tlam_r`) take the annotation equation
  and the right annotation's well-formedness.
- Semantics: `VS_ulam`, `VS_clam` take the validity of `T ≅ T'` and relate
  the right annotation to the left type (escape), retyping the right
  side's reductions (`tmred_conv`). `VS_tlam` now allows a different, equal
  binder context on the right (as `VS_tpi` does); its η body uses
  `tmred_teta_body_ctx`. New helpers: `kw_body_eqty`, `inst_eqty` and
  friends in MInst.
- C1: `synth` excludes only `λ` and `box`; the abstractions synthesize
  (`sy_ulam`, `sy_clam`, `sy_tlam`); `nlr` and its premises are removed.
  A checked head of `uapp`/`capp`/`tapp` (`λ` or `box`) has the wrong
  former and is refuted by head discrimination.

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

Status: P ⊆ O done (K3, K4); O ⊆ P left open (K5). The divergences (ours = O, the
paper's ch. 4 = P) were inventoried and reevaluated first (K1, K2).

#### K1. Divergence inventory (from a full read of ch. 4 against `Declarative.v`)

Representation (same judgments, other encoding):
1. De Bruijn indices; universe variables as `gctx_uwk n`/`Γ⟨ush n⟩ᵤ`
   instead of `L, ℓ⃗`; the motives' `ℓ` as a level binder (`lvren _ (ush 1)`).
2. Local substitutions: one `lshift k` for P's `·^k`, `·_g^k`, `wk_g^k`
   (tail by `lsub_tail`), and global variables require canonical syntax
   (`dnfl`: no absorbable trailing `x/x`). P's syntax admits the
   non-canonical `wk_g^{k+1}, x/x`; O rejects it.
3. The substitution judgments `Γ ⊢ δ : Δ`, `Γ ⊢ δ ≈ δ' : Δ` are replaced by
   entrywise lookup premises (`∀ n A k, in_ctx Δ n A k → …`).
4. Recursors: branches packed by `mkrb`, scopes schematic (`RecSpec`:
   `brG`/`brΓ`/`brRes`/`brLv`), β by the reduct functions `redT`/`redt`
   (P's per-head rules are derived lemmas). The `λ`/variable β read the
   index's whnf, not a literal `Π` (derivable in P by index congruence).
5. C1b: `ulam`/`clam`/`tlam` carry their former (P's `TLAM` has no `Δ`).
6. Level equivalence is semantic (equal evaluation), P's is the axioms of
   ch. 4 §Universe Levels. The axioms are complete, so the two agree on
   well-formed levels (K3, `leqP_iff`).

Extra premises, admissible (logrel-coq style):
7. Explicit reflexivity instead of P's per-former congruences
   (`Nat ≈ Nat`, `x ≈ x`, `0 ≈ 0`, code congruences).
8. Left well-formedness premises on congruences: `eqty_pi` (`A`; P's Π
   congruence has none), `eqtm_code_pi` (`s`), `eqtm_natrec` (`M`),
   `eqty_CTrm` (`Δ`, `T`), `eqty_cpi`/`eqty_tpi`/`eqty_upi` (`T`), the
   abstractions, letbox, recursors. Stability/functionality type the right
   body in the extended context with them.
9. Right-side premises (M5 G2, letbox): `eqty_tpi` (`T'`), `eqtm_tlam`
   (`T'`, `t'`), `eqtm_letbox*` (`M'`, `t2` under `Δ'`). Reason then: no
   global-context conversion. Now there is (`GConv`, `gbind_*`).
10. Instance premises (M3 E10, M5 G2): recursor result type, recursor
    congruence motive-instance equation, recursor β reduct typing,
    `capp`/`tapp` result type and instance equation. Reason: functionality
    precedes global substitution. Admissible since M6 H8
    (`declM_inst_*_eq`, `declM_mot*_eq`) and A2 (subject reduction), both
    via the FT.
11. Recursors: branch-context well-formedness (`brΓ k`, `k < 13`).
12. `box` congruence: `≡ₗ` premise (M3 E11; admissible by A3), both sides
    typed at C, `Δ`/`T` well-formed.
13. Context equivalence: O's `eqc_ext` has fewer premises (left only) than
    P's (both sides typed and equal in both contexts).

Extra rule:
14. `eqty_leq`/`eqtm_leq` at M (M3 E12). Load-bearing in the early
    metatheory: `UInst.v` (instantiation at equivalent level lists, before
    `GConv`), and via `leq_eqty`/`leq_eqtm` in `DeclInstance`,
    `AlgInstance`, `AlgSound`, `Payload`.

Gaps and typos in P that a transcription must settle:
- recursor congruences are not written ("propagate inwards");
- recursor β rules are listed selectively;
- `letbox` scrutinee typed `@ 1 + l` (Typ) and `@ l` (Trm); should be `0`;
- the `Π` β of `elim_Typ` concludes with `M_Trm` (should be `M_Typ`);
- the `UΠ` formation premise is at layer "1" (should be M).

#### K2. Reevaluation (user decision: do the two removals first)

- Representation (1–6): keep. P over our syntax keeps canonical
  substitutions (`dnfl`) on both sides; levels stay semantic in O, and
  completeness of P's level axioms is a separate lemma (from `LevelDec`'s
  normal form).
- 12, the `≡ₗ` premise of the `box` congruence: remove. The metatheory
  only transports it; its one consumer, the FT's `box` case, gets it from
  `static_code_eq` (A3). The rule becomes the paper's.
- 9, right-side premises of `eqty_tpi`, `eqtm_tlam`, `eqtm_letbox*`:
  tried; kept (see "As built").
- 10, instance premises: keep. Admissible only through the FT; removing
  them would need syntactic global functionality.
- 7, 8, 11, 13: keep (logrel-coq style; presupposition derives them).
- 14, `eqty_leq`/`eqtm_leq`: keep in O (used before `GConv`); C3 proves
  them admissible in P.

As built:
- 12 done. `eqtm_boxT`/`eqtm_boxt` take the C-equation (and both sides
  C-typed) only. The metatheory went through unchanged: it only
  transported the premise. `FM_boxT_eq`/`FM_boxt_eq` take the C-equation
  and get `≡ₗ` from `static_code_eqty`/`_eqtm`. The primed rules
  `eqtm_boxT'`/`eqtm_boxt'` (A3) are gone.
- 9 tried and reverted; the premises stay. Removing them breaks nothing
  up to global substitution (weakening, substitution, functionality and
  global substitution only transport them). Two consumers need them:
  - `presupposition`, which must type the right body at the right
    binding. That needs global-binding conversion (`gbind_*`, today in
    `Validity/AlgPrereq.v`, after the FT) inside the presupposition
    induction. It would work by stratifying: presupposition below M first,
    then `gbind` from it, then presupposition at M.
  - the FT (`FM_tpi_eq`, `FM_tlam_eq`, `FM_letbox*_cong`), which uses the
    premises' validity at the right binding. Without them it needs a
    semantic `gbind` (validity under `U : Δ` gives validity under
    `U : Δ'` for valid `Δ ≅ Δ'`), which doesn't exist.

  That is a lemma-order restructure plus a new semantic lemma, only to
  change the rules' shape. C3 doesn't need it: after the FT, `gbind_*`
  derives the premises, which is what P ⊆ O uses.

#### K3. Level equivalence (done, `Syntax/LevelAx.v`)

P's `L ⊢ l ≈ l' : Level` (04:251) is the inductive `leqP`: the PER rules,
congruence for `1+` and `⊔`, and the six algebraic rules, verbatim. P's
well-formedness judgment (04:229) is our `lwf` as is.

- `leqP_iff : leqP L l l' <-> lequiv L l l'`. Soundness: each rule is a
  Level.v lemma. Completeness: every well-formed `l` is `leqP`-equal to
  the normal form `nf L (leval lz l) (loff l)` = `c ⊔ (⊔_{x<L} k_x + x)`
  (`leqP_nf`; absent variables are `0`). The data `(leval lz l, loff l)`
  is what `leqv_iff` (LevelDec, M6 H3) says `leqv` determines, so
  equivalent levels have the same normal form. This is the paper's
  `flatten (adjust (count l))` (04:410) without `adjust` (the redundant
  constant stays; it is absorbed by the algebraic rules either way).
- Corollaries: `leqP_lvsubst` (04:392) and `leqP_dec` (04:350), via the
  semantic side. Closed under the global context.

So P's rules can use `leqP` and O's `lequiv` is interchangeable with it:
item 6 of K1 (semantic levels) is no longer a divergence of the judgments,
only of their definition.

#### K4. P as an inductive, and P ⊆ O (done)

- `Typing/Paper.v`: P's judgments (`pwf_*`, `peq_*`, notation `⊢ₚ`,
  scheme `ptyping_mut`) over our syntax, with K1's representation
  (items 1–5) and the paper's rules: no reflexivity (a congruence per
  former, including `Nat`, variables, `0` and the codes), the paper's
  premises only, no instance or scope premises, no `≡ₗ` rule, the
  paper's context equivalence, `leqP` for levels. The file header lists
  how K1's gaps and typos are settled. Choices beyond K1's list:
  - the `El` decoding rules take `compt i`: the paper states them among
    the MLTT rules without it, but at C they would contradict its Static
    Code Lemma (05:1055);
  - the `UΠ`/`ULAM` congruences take `⊢ Γ` (the paper's omit it; getting
    it from `Γ⟨ush n⟩ᵤ` needs a universe strengthening we don't have);
  - the recursors' β: one schematic rule per recursor, premised on the
    redex's P typing (which packs `G_A`, `⊢ Δ` and the code's typing);
  - the recursors' congruences: every component's equation, typed in the
    left scope, like the paper's other congruences.
- `Typing/PresupC.v`: presupposition of equations at V and C
  (`presupposition_C`, `eqty_wf_C`, `eqtm_wf_C`). O's presupposition only
  covered `typeof i = i`; the paper's `box` congruences take only the
  code's C-equation. Right-hand sides move by context conversion along an
  equivalence at D (`CtxConv`), types by equations at D; the term `gvar`
  case needs functionality at D.
- `Validity/PaperSound.v`: `paper_sound`, P ⊆ O for all seven judgments,
  by induction on P. The P rules with fewer premises than O's are
  lemmas `ps_*`: presupposition (D/M, `PresupC`), type inversion
  (`inv_ty_upi`/`cpi`/`tpi`), `gbind_*` for the right-hand bodies of
  `TΠ`/`ΛU`/`letbox` (`move_tybind`, `gbind_obj_tm`), `RecAdm` and
  `branch_conv` for the recursors' scopes, `declM_inst_*_eq`/
  `declM_mot*_eq` for the instance equations, subject reduction for the
  recursors' β reducts. So K2's reasoning held: O's extra premises are
  all derivable after the FT. Closed under the global context.
- Corollaries: `paper_consistency`, `paper_canonicity` (reduction to a
  canonical value; the equation with it is O's until O ⊆ P).

#### K5. O ⊆ P: analysis, left open (user decision)

O ⊆ P would transfer O's decidability and the canonicity equations to P.
It needs more than planned. By induction on O derivations, with P's
reflexivity carried in the motive, most rules go through; two do not:
- O's `eqc_ext` has fewer premises than P's (P wants the entry equation
  and the right entry typed in the right context). Workable by
  stratifying: D/C derivations contain no context equivalence and no M
  judgment, so first O ⊆ P below M, then context equivalence at D by O's
  context conversion and that result, then M (whose context equivalences
  are all at D), then context equivalence at M likewise.
- O's `≡ₗ` rule at M (`eqty_leq`/`eqtm_leq`). "Lemma L" (induction on
  the left side, the right side O-typed) works for every former except
  global variables: P's `gvar` congruence needs the right substitution's
  entries P-typed, and P typing of `≡ₗ`-variants needs context conversion
  along `≡ₗ`-related entries, hence P weakening (the variable case needs
  the weakened entry's P typing). P weakening in turn needs P's global
  and universe weakening for the bodies under global binders and `UΠ`
  (their target contexts), i.e. a port of `Properties.v`'s weakening,
  `GWeakening.v` and the universe weakening, or one Kripke-style
  induction over all three.
- The LR route (a generic-equality instance given by P equality) needs
  the same P weakening laws, and its conversion law takes an O type
  equation, which would need O ⊆ P for types first.

Decision: stop C3 at P ⊆ O. Everything but the `≡ₗ` rule is a moderate
proof along the stratification above, if wanted later; it would not
transfer decidability, since O's algorithmic soundness uses `eqtm_leq`.

### C4. An executable checker

A fuel-based, `Type`-valued decision procedure for conversion (M6 H1)
and, with C1, type checking, as in logrel-coq.

Status: to design.

## Order

A1, A3, B1, A2, B2, C1, C1b: done. C3: P ⊆ O done, O ⊆ P left open (K5). Next:
C2–C4, each designed when reached.
