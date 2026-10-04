# M9: bodied globals (Heather's definitions), design

Status: done, 2026-09-29 (fork settled (b) by the user; outcome at the end). The rules are Heather's (`H/docs/metatheory-ch07-extensions.md`
Part IV, §23–26); the ch. 07 obligations are its open issue
`H/issues/metatheory-ch07-definitions.md`. No paper pass exists: this
milestone is the first check of them.

## What Heather specifies

- **Binding.** `u : Trm_c(Δ ⊢ T @ l) := t`, extending `⊢ Ψ` (wf-def):
  `Ψ ⊢_p Δ`, `Ψ; Δ ⊢_p T @ l`, and the body `Ψ; Δ ⊢_c t : T @ l`, at the
  binding's own layer, which must be C. Type globals `U` get no bodies.
- **Use.** Unchanged: `Ψ; Γ ⊢_j u^δ : T[δ] @ l` for `c ≤ j`, the `gvar`
  rule.
- **δ.** At the computing layers only: `u^δ ⇝ t[δ]`. `u^δ` is not neutral
  at D/M when `u` is defined, and stays neutral at C. Reduction never
  enters `box`, so δ never reaches code; `box(u^δ)` and
  `elim(box(u^δ))` stay stuck, as ch. 06's neutral grammar has them.
- **Owed (§26).** (1) glueing: at D/M the relation interprets a defined
  `u` by its body; (2) at C nothing changes, and the two readings cohere
  across `□`; (3) the fundamental theorem's global cases split on
  definedness; (4) δ terminates (Ψ is a telescope).

## How our development reads it

Our relation is reduction-based (whnf, Kripke over global weakenings), so
δ must be a *reduction*, not only a declarative equation: a defined `u^δ`
at D/M has to weak-head-reduce, or it would sit in the neutral relation
while being equal to a canonical form. Glueing (1) is then anti-reduction
plus the body's validity; (4) is free, because normalization comes out of
the relation. Where the body's validity comes from: N1.

Global substitutions (`letbox`'s `gsingle`, the recursor's `gbsub`) never
bind a definition, only rename it. So a global substitution is required to
send a defined global to a defined global whose body is the substituted
body (`σ u = GId j`, `Ψ'(j) = u's body⦃σ⦄`). Every substitution we build
already does; the condition goes into `gsub_wf`.

## The fork: where δ finds the body

`red`, `whne`/`whnf` and everything built on them (37 files) are
context-free today: `red t t'` has no `Ψ`.

**(a) Reduction reads Ψ.** `red Ψ t t'` with `red_delta : Ψ(u) = t_u →
red Ψ (gvar u d) t_u[d]`, and `whne Ψ (gvar u d)` only when `u` has no
body. Syntax as in Heather. Every statement about reduction and normal
forms gains `Ψ`, and every lemma relating reductions across global
contexts (weakening, global substitution) carries a condition that the
contexts' bodies agree. The existing `gvar` cases (the heaviest case in
most metatheory files) split on definedness everywhere.

**(b) An occurrence carries its body.** A new term former `gdef u t d`:
the global `u`, its body `t` (weakened to the occurrence's `Ψ`, as
`in_gctx` weakens a declaration), and its instance `d`. Typing:
`in_gctx Ψ u (gdDef Δ T l t)` plus `gvar`'s premises gives
`gdef u t d : T[d]`. Reduction stays context-free: `gdef u t d ⇝ t[d]` is
one more β-like rule, `gdef` is never neutral at D/M, and at C it is inert
code (no reduction there), so `box(gdef …)` and `elim(box(gdef …))` are
stuck as ch. 06 wants (two neutral productions, like `gvar`'s). Existing
`gvar` proofs do not change; the new cases live with the new former, whose
cost L5/J1 made small. Departure from Heather: its `u^δ` elaborates to our
`gdef u t δ` when `Ψ` defines `u` (and to `gvar u δ` otherwise); the
translation is total and preserves typing, and code comparison (`box`)
compares the bodies too, which is harmless because one `u` has one body.

Both need the same `gsub_wf` condition, the same new `gdecl` constructor
(`gdDef Δ T l t`) and `wfg_def`, and the same valid-global-context
induction. The difference is where the body is read.

**Recommendation: (b).** It keeps reduction, normal forms and the
existing `gvar` metatheory as they are, turns δ into a local rule like β,
and puts the new work in new cases, where L5 made it cheap. (a) is more
literal but touches every reduction statement and splits the heaviest
existing case in every file. The price of (b) is a recorded syntactic
departure with a total translation.

## N1. The body's validity comes with the occurrence (taken)

`wf_gdef` carries, besides `gvar`'s premises, the body's typing at the
occurrence's layer: `[ G ; Δ ⊢[ j ] t : T @ l ]`. It is derivable from
`⊢ Ψ` (the body is checked at C in its prefix; lift to `j ≥ C`, weaken to
`Ψ`), so the rule set is equivalent to Heather's; the premise only puts
the body's derivation where the inductions see it. The fundamental
theorem's `gdef` case then gets the body's validity from its induction
hypothesis, at the same layer, and needs no separate valid-global-context
induction. (Our fundamental theorem at D covers D-derivations only, so a
premise at C would not do.)

## N2. The carried body is the declared one up to level equivalence (taken)

Code is compared up to level equivalence (`tm_leq`, M3 E11), and the
Static Code Lemma makes every level-equivalent variant of well-typed code
well typed. An occurrence `gdef u t d` whose body had to be *identical*
to Ψ's would break that: a variant carries a variant body. So `wf_gdef`
asks `tm_leq t₀ t` against the declared body `t₀`, the congruence
`eqtm_gdef` relates `gdef u t d` and `gdef u t' d'` given `t ≅ t'`, and δ
unfolds the carried body. Level equivalence is equality under every
valuation of the levels, so the carried body means the declared one.

## Plan (for (b))

1. **Syntax.** `gdef`, `gdDef`; every operation's case (L5's lists: push
   lemmas, dnf, level equivalence).
2. **Typing.** `wfg_def`, `wf_gdef`, congruence `eqtm_gdef`, δ
   `eqtm_delta` (computing layers). Metatheory (weakening, substitutions,
   presupposition, inversion, Static Code: `gdef` at C is code).
   `gsub_wf`'s condition for `gdDef`.
3. **Reduction.** `red_delta`; `whnf` for `gdef` at D/M is not neutral;
   `whne_elimt_gdef` (boxed `gdef` blocks the recursor, like `gvar`).
4. **Recursor.** At C `gdef` is code: a branch, or stuck like `gvar`?
   Heather has no branch for `u^δ` (ch. 06's neutral grammar; its
   `opaque-globals-analysis` round confirmed it). So stuck: no new branch.
5. **Relation.** Valid global context (bodies valid), stable under global
   weakening; the fundamental theorem's `gdef` case by anti-reduction.
6. **Algorithm.** δ in weak-head reduction; conversion unchanged in shape
   (Heather's δ-lazy order is a strategy, §25, not a rule).
7. **Consequences.** Canonicity (closed terms may now mention defined
   globals: canonicity for `ctx_only` global contexts stays; one with
   definitions is the new statement), consistency, decidability.

Measure against M8's per-former cost; record in this file.

## Outcome

Built as planned for (b), with N1 and N2. Full build green, no admits;
`consistency`, `tyd`, `ckd`, `ac_tm_dec`, `decl_eqtm_dec_any` and
`closed_canonicity` are closed under the global context.

- **Syntax and typing** as in the plan. Global substitutions send a
  definition to the same definition (`GObjRel gdDef = GId`, `gobj_wf`),
  so `letbox` and the recursor never bind one.
- **Reduction.** `red_delta : gdef u t d ⇝ t[d]`; `gdef` is not neutral;
  `whne_elimt_gdef` keeps `elim(box(gdef …))` stuck. The recursor's stuck
  law and the algorithmic rule are generalized from `gvar` to
  `boxed_global c` (a `gvar` or a `gdef`), compared up to `tm_leq`: one
  rule and one lemma per algorithmic family instead of two.
- **Relation.** `Validity/Delta.v` (104 lines): δ is anti-reduction plus
  the body's validity at the related local substitutions (N1 gives the
  body's derivation at the use layer, so the fundamental theorem's IH
  covers it). No valid-global-context induction was needed. Heather's §26
  bill: (1) glueing = `VS_delta`/`FS_delta`/`FM_delta`; (2) coherence
  across `□` is structural: reduction never enters `box`, and at C `gdef`
  is inert code; (3) the `gdef` cases of both fundamental theorems;
  (4) termination is normalization, which the relation gives.
- **Algorithm and decidability.** δ is one more weak-head step; type
  checking synthesizes `gdef` (`sy_gdef`: `gvar`'s premises, `tm_leq` to
  the declared body, the body checked at the use layer), and `⊢ Ψ` with
  definitions is decidable.
- **Canonicity.** At D, closed canonicity now holds in global contexts of
  context variables *and definitions* (`closed_ok`, `no_closed_neutral_D`).
  At M it stays for context variables only: `elim(box(u^δ))` with `u`
  defined is a closed neutral (Heather keeps it stuck, step 4). This is a
  consequence of Heather's design worth knowing: a closed M-program that
  runs the code recursor on a boxed definition does not compute. It bears
  on `opaque-globals-analysis` (a recursor branch for `u^δ`, or unfolding
  for analysis). Not machine-checked: a concrete typed instance.
- **Not proved here.** N1's premise is derivable from `⊢ Ψ` (body at C in
  its prefix, lifted and weakened); argued, not proved. Consistency still
  assumes `ctx_only` (since settled: Follow-up, item 3).

**Cost.** 64 files, about 990 lines added and 240 changed, against about
4000 in 56 files for Σ (M8a). By area: syntax and substitution laws
~150; typing rules and their metatheory ~350; the relation and both
fundamental theorems ~350 (`Delta.v`, `FundamentalS/M`); the algorithmic
side mostly renames (`gvar` → `glob`); type checking, type uniqueness,
preservation, canonicity ~150. The L5 rule lists kept most metatheory
entries to one line; the new cases cluster in the files with manual
dispatch (GSubstitution, GWeakening, Presupposition, the two fundamental
theorems).

## Follow-up: open items 1, 3 and 4 (2026-10-04)

Full build green, no admits; `closed_canonicity_fails_M`,
`stuck_rec_not_numeral`, `unfolding` and `consistency_def` are closed
under the global context.

- **Item 1, the witness** (`Validity/DefStuck.v`). `Ψ = (u : Trm(· ⊢ Nat)
  := zero)` and `elim_Trm(x. Nat; 0, …, 0; box(u^id))` at `Nat`, every
  branch `zero`. It is typed (`stuck_rec_wf`, through `wf_elimt_adm`),
  neutral, has no value (`stuck_rec_no_value`) and is not even
  judgmentally equal to a numeral (`stuck_rec_not_numeral`: the relation
  at `Nat` pairs a neutral only with a neutral). `Ψ` has no opaque
  binding, so `closed_canonicity_fails_M`: `closed_ok` cannot extend to M.
- **Item 4, the D statements.** `closed_nat_canonicity`,
  `decl_closed_nat_canonicity`, `closed_nat_canonicity_c`,
  `paper_canonicity`, `neutral_univ`, `no_type_var_inhabitant`,
  `consistency(_closed)` take `closed_ok i G` (at M it is `ctx_only`,
  `closed_ok_M_ctx_only`). The `declM_*` statements stay at `ctx_only`.
- **Item 3, consistency with definitions: holds at D and M**
  (`Validity/ConsistencyDef.v`, `consistency_def`): no term of
  `Π (x : Ty ℓ). El x` in a global context of context variables and
  definitions (`no_opaque`) and a local context of universes, at either
  computing layer; `paper_consistency` now takes `no_opaque`. So the stuck
  recursor of item 1 is a computational defect, not a logical one. The
  proof is a translation, not a new relation:
  - `unf` (`Syntax/Unfold.v`) inlines every occurrence `gdef u t δ` as
    `t[δ]`, everywhere, code included. It commutes with every syntactic
    operation (one mutual induction per law, as in `Subst.v`), its outputs
    mention no definition (`unf_gfree`), and reduction keeps terms
    definition-free (`gfree_red`).
  - `unfolding` (`Typing/Unfold.v`): every judgment under `G` holds,
    unfolded, under `unf_G G` (bindings unfolded, still `no_opaque`). The
    occurrence rule becomes the substitution lemma applied to the carried
    body (N1 is what makes this local: the occurrence's own premise types
    the body at the use layer), its congruence becomes substitution plus
    functionality, and δ becomes reflexivity. The recursor β cases need
    the bundle to be `mkrb` (`inv_elimT`): peeling commutes with `unf`
    only at binder heads (`hd_ok`), as for local substitution.
  - `consistency_gen` (`Consistency.v`): `neutral_univ` and its two
    consequences now take `no_opaque G` and, per term, `closed_ok i G \/
    gfree_tm t`. A definition-free neutral cannot hide a stuck
    `elim(box(u^δ))`, and the whnf of a definition-free term is
    definition-free.
- **One change to the syntax.** `pdef`, the instance of `gdef u t δ` under
  a global substitution sending `u` to a non-variable object, used to be
  `gdef`'s junk; it now inlines the carried body (`t[δ]`). Typed
  substitutions never send a definition there (`gobj_wf`), so no
  judgment changed, but `unf` then commutes with global substitution
  unconditionally.

**Heather findings.** (1) With definitions, M has closed stuck programs:
a recursor run on a boxed definition does not compute and is not equal to
any value, now with a checked instance (`opaque-globals-analysis`).
(2) Consistency is unaffected, at D and M. (3) The unfolding argument is
exactly "unfold definitions for analysis" applied to a whole derivation:
inlining every definition, inside code too, is a typing-preserving map to
the definition-free system. That supports unfolding as the answer to the
stuck recursor, as a whole-program translation. An in-place rule
`elim(box(u^δ)) ⇝ elim(box(t[δ]))` is a different claim, not checked
here: at C, code equality relates `u^δ` only to `u^δ'`.

**Cost.** `Syntax/Unfold.v` ~640 lines (most of it the laws, mechanical
after `Subst.v`), `Typing/Unfold.v` ~410 (the theorem's proof is the
generic rule dispatch plus 13 manual cases), `ConsistencyDef.v` 50,
`DefStuck.v` 120.

## Open items (for later rounds)

What M9 argued rather than proved, or left at the old scope. None blocks
M10; each is a standalone round. Ordered by value to Heather first.

1. **The M-canonicity witness.** Done (Follow-up). Build a concrete typed instance: a global
   context with one definition `u := t` (say a closed `Nat` code), and the
   closed M-term `elim_Trm(box(gdef u t ·))` with some motive and branches.
   Show it is typed, `whne` (`whne_elimt_gdef`), and not canonical, so
   `closed_ok` cannot extend to M with definitions. This turns the
   Outcome's canonicity finding into a checked counterexample for
   `H/issues/opaque-globals-analysis.md`, which Heather closed its
   definitions issue citing our check.
2. **N1 is admissible.** Prove the premise `wf_gdef` adds (the body typed
   at the use layer) is derivable from `⊢ Ψ`: the body is checked at C in
   its prefix, lifted to `j ≥ C`, weakened to `Ψ`. With it, prove that the
   translation from Heather's syntax (`u^δ ↦ gdef u t₀ δ` when `Ψ` defines
   `u`, `gvar u δ` otherwise) is total and preserves typing, the claim (b)
   rests on. Needs a lifting lemma C → j for terms and global weakening of
   the prefix; check what `StaticCode.v` and `GWeakening.v` already give.
3. **Consistency with definitions.** Done (Follow-up): it holds at D
   and M. `consistency` and
   `no_type_var_inhabitant` (`Validity/Consistency.v`) still assume
   `ctx_only`. At D, `no_closed_neutral_D` suggests the same proof goes
   through with `no_opaque` (`neutral_univ` is the lemma to generalize).
   At M it is open: a stuck `elim(box(gdef …))` is a neutral whose type
   is the motive at a stuck code. Whether it can inhabit `El x` in a
   context of universe variables needs an argument: every branch but
   the stuck one would also have to inhabit the motive, and the motive
   at the stuck code is a stuck type, not `El x`. Settle it or find the
   counterexample; either is a Heather finding.
4. **Canonicity statements at the old scope.** Done (Follow-up).
   `closed_canonicity` takes
   `closed_ok`, but these still take `ctx_only`:
   `closed_nat_canonicity` (`Consequences.v`), `decl_closed_nat_canonicity`
   (`DeclConsequencesP.v`), the three `declM_closed_*_canonicity`
   (`DeclConsequences.v`), `closed_nat_canonicity_c` (`Uniform.v`),
   `paper_consistency` and `paper_canonicity` (`PaperSound.v`). Generalize
   the D ones to `closed_ok`; the M ones stay at `ctx_only` by item 1.
5. **A Heather-faithful rule set.** `Typing/Paper.v` (M7 C3) transcribes
   the paper's rules and has no definitions. Heather's `u^δ` with δ
   reading `Ψ` could be written there as a second faithful system and
   shown equivalent to ours through item 2's translation. Low priority:
   item 2 is the substance.
