# M9: bodied globals (Heather's definitions), design

Status: proposal. The rules are Heather's (`H/docs/metatheory-ch07-extensions.md`
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
the relation. Where the body's validity comes from: a **valid global
context**, each body valid at D in its prefix, proved by induction on
`⊢ Ψ` from the fundamental theorem of the prefix, and moved to longer
contexts by the relation's Kripke invariance under global weakening.

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
