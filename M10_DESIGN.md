# M10: strict equality (`sEq`, `srefl`, `transp`, `sEmpty`), design

Status: **M10a done, 2026-09-29** (outcome at the end). M10b is
blocked: the strip is Werner's rule, whose normalization in a predicative
theory is an open problem (S5). The candidate of S4, (D), fails.

Heather's rules: `H/docs/sprop-design.md` (frozen rule set, §2–§6). Its
paper pass: `H/docs/metatheory-ch07-extensions.md` Part III, §18–22 (MX
below). That pass names §19.4's substitution lemma as the first thing to
recheck before any mechanization (MX §22.5, caveats). Here the weak spot
turns out to be one step earlier, at §19.2.

## What Heather specifies

- **Formers.** `sEq^l(I; a; b) : Ty l` (`Id`'s shape), `sEmpty^l : Ty l`
  (level-indexed like `Unit^l`), codes `TmSEq`/`TmSEmpty` decoded by `El`.
- **Terms.** `srefl^l(I; a) : sEq^l(I; a; a)`, the only canonical form;
  `transp^{l,l'}(I; x.P; a; b; e; t) : P[b/x]` for `t : P[a/x]` (J's
  non-dependent cousin, no motive over the proof);
  `elim_sEmpty^{l,l'}(M; e) : M`, neutral only.
- **Irrelevance laws.** Any two terms of `sEq^l(I;a;b)` are equal, and so
  are any two of `sEmpty^l`. These are rules without premises, like
  η-`Unit` (our `eqtm_triv`/Unit η, M8c).
- **β.** `transp(…; srefl; t) ≈ t`.
- **The strip rule**, a declarative equation:
  `Γ ⊢ a ≈ b : I @ l  ⟹  Γ ⊢ transp^{l,l'}(I; x.P; a; b; e; t) ≈ t : P[b/x]`.
  Given the irrelevance laws, the strip already follows from β: from
  `a ≈ b`, `e ≈ srefl` by irrelevance, then β applies. So once `transp`
  exists with β, the strip is not optional.
- **Layers.** MLTT formers: types at every layer but V, the computation
  rules (β, strip, irrelevance) at the computing layers. The strip never
  enters a `box` (MX §19.5).

## The semantics MX asks for

MX §19.1 changes the evaluation relation instead of adding clauses. `⇝ₛ` is
ch. 06's weak-head reduction plus the strip as a reduction step, under
its declarative premise `Γ ⊢ a ≈ b`. The congruence step that reduces
`transp`'s proof is restricted to the complementary premise `Γ ⊬ a ≈ b`,
so reduction stays deterministic (§19.3). Every term and type relation is
read over `⇝ₛ*`. A stuck `transp` (endpoints not convertible) is a
neutral, and the neutral clauses see only strip-normal terms (§20.3).
§19.4 weakens substitution to joinability.

## Where this meets our development

Three facts about our side fix the shape of the problem:

- `red` is untyped and context-free (`Syntax/Reduction.v`), and so are
  `whne`/`whnf` (`Syntax/NormalForms.v`). The relation reads reduction
  through `tmred`/`tyred` (`Typing/TypedRed.v`), which already carry
  `G`, `Γ` and a declarative equation. So a context-dependent step fits
  there without making `red` itself depend on the context.
- The relation is Kripke over weakenings (`kwk`: a global weakening, then
  a local one), and its monotonicity rests on normal forms surviving
  renaming (`whne_ren`, `whnf_ren`, `whne_gwa`, `NormalForms.v`,
  `GWeakening.v`). Determinacy of reduction to a normal form
  (`reds_whnf_det`, `tmred_whnf_det` and their type variants, about 80
  occurrences in 17 files) is what the irrelevance proofs line up on.
- The development is axiom-free (`Print Assumptions` closed), including
  the decidability results `ac_tm_dec` and `decl_eqtm_dec_any`.

### S1. Finding: MX §19.2's proposition is a strengthening lemma

Under `⇝ₛ`, strip-normality of a stuck `transp` at `Γ` is the negative
condition `Γ ⊬ a ≈ b`. Monotonicity needs it to survive every Kripke
weakening `ρ : Δ ≤ Γ`. That means from `Δ ⊢ a⟨ρ⟩ ≈ b⟨ρ⟩` we must
conclude `Γ ⊢ a ≈ b`: **strengthening** of declarative convertibility,
for local and for global weakenings. Without it, a term that is stuck at
`Γ` can strip at `Δ`, `reds_whnf_det` fails at `Δ`, and the neutral
clause at `Δ` admits a strippable `transp`: the unsoundness MX §20.3
describes.

MX §19.2 states this proposition ("weakening does not create strip
premises") and justifies it by the absence of equality reflection. As an
intuition that is right. As a proof it is missing. With transitivity in
the declarative judgment, a derivation of `a ≈ b` in `Δ` can pass through
middle terms that mention the new variables. Strengthening for
declarative equality is normally a *consequence* of normalization: you
go through a syntax-directed algorithm, which is complete by the
relation. Here the relation needs it first. The easy case does not cover
it: when the new type `A` is inhabited in `Γ`, substituting an inhabitant
for `x` strengthens, but a Kripke weakening may add an empty type
(`x : sEmpty`, `x : sEq(Nat; 0; 1)`).

The same issue appears in MX §20.4's Weakening row ("nothing, *given*
§19.2's proposition") and §21.3's stuck arm, which case-splits on
`a ≈ b` or `a ≉ b`. That split is classical: an FT arm has to decide
declarative convertibility before decidability is known.

The literature is consistent with this being the hard point. The
logrel-mltt branch `impredicativity-cast-compute-refl` (Pujet) keeps its
`cast A B e t ≡ t` for `A ≡ B` *out of* reduction, as an η-like
conversion-time rule, to avoid typed reduction with conversion premises.
The TYPES 2024 implementation (Sirman et al., cited in sprop-design §1)
refuses it as a reduction for determinism and mutual recursion. In both,
though, cast computes on *type structure*, so the rule is only needed at
neutral types, where it can live in the generic neutral equivalence.
Heather's `transp` is J-like and does not compute on its motive, so the
strip is needed at canonical types too (MX §20.3's `transp(…;e;5) ~ 5`
at `Nat`).

This is not a Heather soundness bug. It is a gap in the paper pass, and
it decides how M10b can be done. It should go to Heather's issue
tracker, after we have tried the routes below.

### S2. What does not work (checked on paper)

- **LEM alone.** Classical case splits handle §21.3's arm but not S1:
  the negation still has to survive weakening. LEM would also make the
  `sumbool` decidability statements trivially true. They would have to be
  restated as an explicit algorithm plus a termination proof.
- **A weakening-closed premise** (strip if `a ≈ b` in *some* extension;
  stuck if in *none*). Both conditions are Kripke-stable, the second
  trivially and the first by amalgamating extensions (reorder the extra
  globals, move them through a global substitution). But the equation the
  step must carry (`tmred_eq`) lives at `Γ`, and its presupposition needs
  `Γ ⊢ P[a] ≈ P[b]`: strengthening again.
- **Restricting Kripke to conservative weakenings.** Escape at Π weakens
  by the domain, which is exactly the case in question.

### S3. The fork: how to state the strip (open)

- **(A) Prove strengthening first**, for the declarative system with the
  strip, without normalization. If some syntactic argument exists
  (e.g. via replacing new locals by fresh globals, then an argument
  that an unused global postulate adds no equation), everything else is
  MX as written. Risk: unknown, possibly research-hard. Cheap to probe on
  paper before any Coq.
- **(B) Change the strip premise to a context-free one** (S5: this
  changes only the operational side; the declarative theory is the same
  for every premise). For example,
  `a` and `b` joinable under untyped `⇝ₛ` (which respects renaming in both
  directions, syntactically). This loses the type-directed conversions
  (η at Π/Σ/Unit, irrelevance): `x, y : Unit` would not strip. Heather's
  customer (open `plus(0, n) ≡ n`, route 2b) needs only computation, but
  that has to be checked against `crates/elab/tests/indexed_route_2b.rs`.
  The declarative theory changes, so Heather's rules change. Decidability
  would need reduction and joinability to terminate together, which the
  relation gives.
- **(C) OTT-style `transp` that computes on the motive's instances**
  (whnf `P[a]` and `P[b]`: both `Nat`, both `Unit`, … ⇒ the payload),
  with the strip kept only at neutral instances as a generic-equivalence
  law, as in the logrel-mltt branch. It avoids typed reduction with a
  conversion premise altogether. It fails at Π/Σ/□ motive instances,
  where a structural cast needs type-level equality proofs that a
  term-level `sEq` cannot supply. That makes it a redesign of Heather's
  eliminator (towards CCobs `cast`), not a local change.

Recommendation, tentative: spend a bounded paper probe on (A). If no
argument turns up, choose between (B) and (C) together with Heather's
customer, and record the result in Heather either way.

### S4. The paper check on (A) (2026-09-29)

**No direct proof of strengthening found.** The attempts, and where each
stops:

- *Substitute an inhabitant for the new variable.* This works when the
  added type is inhabited in `Γ`. It fails for exactly the types that
  matter (`sEmpty`, `sEq` at distinct endpoints), and a Kripke weakening
  may add them.
- *Replace new locals by fresh globals.* A local `x : A` at the end of
  `Δ` becomes a global `u : Trm(Γ ⊢ A)`, and `x := u^{id}` is a
  substitution. This reduces local strengthening to global strengthening
  ("an unused postulate adds no equation"), which is the same problem
  one level up. It is still useful: global and local strengthening
  stand or fall together.
- *Induction on the derivation.* Transitivity (and symmetry,
  conversion) pass through middle terms that may mention the removed
  variable, and nothing smaller in the derivation is free of it. This is
  why strengthening is normally a corollary of a syntax-directed
  algorithm, and the algorithm is what the relation is building.

So (A) as stated remains open. The check did find a way around the
circularity:

**(D) Stratify the strip premise by derivation depth.** Index the
declarative judgments by a stage `n`. The strip rule at stage `n+1`
takes its premise at stage `n` (`Γ ⊢ₙ a ≈ b`); every other rule keeps its
stage. Stage 0 has no strip. There is no separate β rule, since β is
admissible once injectivity of `sEq` is known. Every derivation has a
finite nesting depth of strip premises, so the union of the stages is
exactly Heather's declarative theory.

The metatheory becomes one induction on `n`. At stage `n+1`, stage `n`'s
metatheory is already available, and the strip's side condition
`Γ ⊢ₙ a ≈ b` (with `a`, `b`, `I`, `Γ` checked at stage `n`) is:
- **decidable**, from stage `n`'s type checking and conversion, so the
  fundamental theorem's case split is constructive and needs no LEM;
- **stable under weakening in both polarities**, from stage `n`'s
  strengthening, which in turn follows from its syntax-directed
  algorithms (checking, conversion) by induction on their derivations.

So stage `n+1`'s reduction is deterministic, its normal forms survive
Kripke weakening, and the relation, fundamental theorem and decidability
go through at stage `n+1` as MX describes, with `⇝ₛ` read at stage `n`.

What it costs, and what it leaves open:

- A stage index on every judgment. Carrying it in the global context
  record (like `gL G`) keeps the statements unchanged; the strip rule
  reads the premise at the decremented stage.
- Strengthening, local and global, for the algorithmic judgments and for
  typing (via the checker). We have none today.
- **Stabilization, for the union.** At a fixed stage, closed canonicity
  can fail: a closed `transp` whose endpoints are equal at stage `n+1`
  but not at `n` is stuck at stage `n+1`, and strips at `n+2`. Canonicity
  and decidability of Heather's full theory need: for given well-typed
  terms, the answers of stage `k` stop changing beyond some `k`. That is
  plausible (the algorithm's query tree on normalizing terms is finite)
  but not argued yet.

Verdict: (D) is the first candidate that keeps Heather's rules as they
are, with no axiom. The open part is stabilization, not a circularity.
Next step on this track: argue stabilization on paper. If it holds, (D)
becomes the M10b plan. If it fails, the counterexample is a Heather
finding: full-theory canonicity would then depend on it.

**Superseded by S5 (2026-09-30):** (D) fails already at stage 1.

### S5. Second paper pass: (D) fails; the strip is Werner's rule (2026-09-30)

**(D) fails at stage 1.** Each stage's congruence for `transp`'s
endpoints lets the strip fire through equations of that same stage, so
the stages separate nothing. Take `c := transp(Nat; _.Nat; 0; 0; srefl; 7)`:
it strips at stage 1 (`0 ≈₀ 0`) and not at stage 0, which has no strip.
Take `T := transp(Nat; _.Nat; c; 7; e; 5)` with `e : sEq(Nat; c; 7)` in
the context. At stage 1, `T ≈ transp(Nat; _.Nat; 7; 7; e; 5)` by
`transp`'s congruence (`c ≈₁ 7`, and `e`'s type converts), and that
strips to `5`, since `7 ≈₀ 7`. So `T ≈₁ 5`. Stage 1's reduction tests the
raw endpoints at stage 0, `c ≈₀ 7` fails, and `T` is a stuck neutral.
Stage 1's fundamental theorem fails at the congruence rule. Testing the
endpoints' normal forms instead makes the premise depend on stage 1's own
conversion (η, irrelevance), which is the circularity again. In general,
with congruence, the effective strip condition at stage `n+1` is
`a ≈ₙ₊₁ b` as soon as the endpoints' class has a term typed at stage `n`.
The argument that every derivation lives at some stage, so that the full
theory inherits stage-wise strengthening, falls with it.

**The declarative theory does not depend on the premise.** Take any
strip rule whose premise `R` holds reflexively on typed terms, and add
`transp`'s congruence and conversion. Together they derive
`transp(I; P; a; b; e; t) ≈ t` from `a ≈ b`: convert `e` to
`sEq(I; b; b)`, move `a` to `b` by congruence, and strip with `R b b`.
So (B) changes only the operational side, and there it is incomplete
for Heather's theory. For `x : Unit`, `transp(…; x; ⟨⟩; e; t) ≈ t`
declaratively, but it is stuck under joinability. (B) is out, unless
Heather drops the congruence of `transp`'s endpoints.

**The strip is Werner's rule, and its normalization is open.** Heather's
`transp` with the strip is the eliminator in Werner's proof-irrelevant
type theory (LMCS 2008): `Eq_rec A P a b x e ⊳ x if a = b`, which ignores
the proof and tests the endpoints.
- Abel and Coquand (*Failure of normalization in impredicative type
  theory with proof-irrelevant propositional equality*, LMCS 2020,
  arXiv 1911.08174) show that it breaks normalization when propositions
  are impredicative. The counterexample is Girard's, and it diverges only
  under a hypothesis, so open terms fail to normalize. Consistency and
  canonicity are not at stake.
- Their open question (3) is exactly our case: does the rule preserve
  normalization in the predicative case?
- `sprop-design.md`'s introduction says predicativity "keeps us clear of
  the Abel–Coquand failure mode". That is right about the
  counterexample. It is not a proof of normalization.
- Later work avoids the rule. Pujet and Tabareau's CCobs (POPL 2023)
  keeps cast along reflexivity propositional (`castrefl`, Rule
  Cast-Refl), and its cast computes on type structure. The TYPES 2024
  implementation refuses the rule (S1).
- A quick search found nothing since 2020 that settles question (3).

So S1's strengthening is not a missing lemma. Any proof of it amounts to
normalization for Werner's rule in a predicative theory, which is
Abel–Coquand's question. A model without the Kripke quantifier (NbE with
a PER model, where the strip compares read-back normal forms of
context-free values) moves the problem rather than removing it.
Validating the strip there needs values with equal normal forms to be
semantically equal, which is the same substitution and soundness
circularity. I found no way through.

**Options as they stand:**
- **(R) Research.** Try to answer question (3) for Heather. Unbounded,
  and not a formalization step.
- **(K) Canonicity only, with the strip as specified.** A model of
  closed terms has no Kripke quantifier, so S1 does not arise. It proves
  consistency and closed canonicity with `transp` and the strip as
  specified. The stuck arm's split on `⊢ a ≈ b` at closed endpoints
  needs `classic` in `Prop`, a new axiom to flag. It gives no
  normalization of open terms and no decidability. The Kripke
  development (the algorithm, `ac_tm_dec`, `tyd`) would have to leave
  `transp` out, so the result is a second model next to the first.
- **(C) Change Heather's eliminator** (S3), towards CCobs. The cast
  computes on the motive's instances, and the strip either stays only at
  neutral instances or becomes propositional (`castrefl`). This is known
  to normalize in the predicative setting (TTobs, Pujet–Tabareau
  POPL 2022). It is a Heather redesign, to settle against the customer
  (`crates/elab/tests/indexed_route_2b.rs`): closed programs need the
  cast to compute at data instances, which (C) keeps.

This is Heather's call: `issues/sprop-strip-normalization-open.md` in H.

## Staging

**M10a: `sEq`, `srefl`, `sEmpty`, `elim_sEmpty`, irrelevance. No
`transp`.** No fork: without an eliminator for `sEq` there is no strip.
Scope as M8c: layers D and M, gated by `compt i` for the computation
rules.

- Syntax: `tySEq l A a b`, `tySEmpty l`, `srefl l A a`,
  `elimSEmpty l l' M e`; every operation's case (L5's lists).
- Typing: formation and congruences; `srefl`; irrelevance at `sEq` and
  `sEmpty` (premise-free, like Unit η); `elim_sEmpty` and its congruence
  (the motive instances agree by irrelevance, MX §21.4).
- Normal forms: `elimSEmpty l l' M e` is `whne` when `e` is. `srefl` is
  `whnf`.
- Relation: `sEq`'s type relation is `Id`'s shape (reduce both sides,
  generic equality of `I` and of the endpoints). The term relations at
  `sEq` and `sEmpty` **keep weak-head normal forms**, as K5 does for
  `Unit`, not MX §18's total relation. The algorithmic instance needs
  normalization of typed terms, and canonicity at `sEq` (closed `e`
  reduces to `srefl`) is what forces `a ≈ b` for closed proofs. Recorded
  as a semantic choice, like K5.
- Generic laws: irrelevance at the two types (escape cannot come from
  term structure, MX §21.5). Algorithm: two type-directed arms that
  accept, ahead of the structural ones, as `actmnf_unit_eta`.
- Consequences: canonicity at `sEq` (closed ⇒ `srefl`) and at `sEmpty`
  (no closed inhabitant); consistency extends; decidability as before.

**M10b: `transp`**, after S3 is settled: β, the strip, the stuck arm, the
FT arms (MX §21.1–21.3), and §19.4 in whatever form S3 leaves it.

**M10c: codes.** `TmSEq`, `TmSEmpty` and the seven recursor branches in
Heather's order (`ty_seq`, `tm_seq`, `ty_sempty`, `tm_sempty`, `srefl`,
`transp`, `elim_sEmpty`, `H/crates/kernel/src/rec.rs` ~3830–4300). Kept
until after M10b so the branch numbering matches Heather's without a gap.

Measure against M8c (Unit at D/M) and M9; record the costs here.

## M10a outcome

Built as staged, with these decisions (the defaults of the plan unless
marked):

- **Syntax.** `tySEq l A a b`, `tySEmpty l`, `srefl l A a`,
  `elimSEmpty l l' M e` (a non-dependent motive, as Heather's). No
  universe codes yet (`TmSEq`, `TmSEmpty`, their `El` decodings): they
  go with the recursor branches in M10c. Reduction: `elimSEmpty` reduces
  its scrutinee only; it is `whne` on a neutral scrutinee.
- **Rules**, all gated by `compt i`: formation and congruences, `srefl`,
  `elim_sEmpty` and its congruence, and proof irrelevance at `sEq`
  (`eqtm_seq_irr`) and at `sEmpty` (`eqtm_sempty_irr`). `srefl`'s
  congruence (`eqtm_srefl`) is a rule although irrelevance derives it,
  as `⟨⟩`'s is: the substitution lemmas then need no conversion of
  `srefl`'s type.
- **Relation** (`LRseq`, `LRsempty`). `sEq`'s type relation keeps only
  the generic equalities of the carrier and endpoints, not the carrier's
  relation: no term relation reads it, so the `Id`-shaped Kripke carrier
  relation of MX §18 would be dead weight. Recorded as a deviation from
  MX. The term relation at `sEq` keeps weak-head normal forms
  (`SEqRel`, as K5). At `sEmpty` the terms reduce to neutrals each related
  to itself (`SEmptyRel`), never to each other: the eliminator's neutral
  law needs neutral scrutinees and compares nothing else. MX §18 has
  total relations at both; ours keep what normalization and the
  algorithm need.
- **Generic laws.** Congruences of the two types, the two irrelevance
  laws (escape at both types comes from them, MX §21.5), and
  `gne_tm_elimSEmpty`, whose scrutinee premises are self-relations.
- **Algorithm.** `actnf_seq` compares endpoints at the left carrier;
  `actmnf_seq_irr`, `actmnf_sempty_irr` accept any two weak-head normal
  forms (neither type is `posty`); `actmne_elimSEmpty` compares motives
  and asks only that the scrutinees be `whne`. A first version asked
  each scrutinee to be algorithmically related to itself; that premise
  does not survive the `≡ₗ` inversions of `AlgStruct` (the right side's
  variant is not self-related without symmetry and transitivity, which
  come later). `whne` does, and it suffices for soundness because the
  instances supply typing and irrelevance supplies the equation.
  Decidability needed `whne` decided (`is_whne`, `whne_dec` in
  `AlgDec`).
- **Consequences.** `closed_sempty_empty`: no closed proof of `sEmpty`
  (at D and M, `closed_ok`). `closed_seq_canonicity`: a closed proof of
  `sEq^l(A; a; b)` computes to `srefl`, and then `a ≅ b`. This is MX
  §18's "sEq imports no equation" for closed terms, now checked. Type
  checking, uniqueness of types, preservation, decidability of
  conversion all extend; `consistency`, `closed_canonicity`, `tyd`,
  `ckd`, `ac_tm_dec`, `decl_eqtm_dec_any` stay closed under the global
  context.

**Cost.** 50 files, about 1450 lines added (170 of them the new
`Validity/SEq.v`) and 60 changed, against 803 in 53 files for Unit at
D/M (M8c) and about 990 in 64 files for M9. Two formers and five
algorithmic rules, so per former it is below M8c. The bulk: the
algorithmic families (PER, decidability, soundness, conversion: about
310), the relation's properties (Escape, Irrelevance, LevelInv and the
rest of LogRel: about 400), Static Code and presupposition (about 110).
The L5 rule lists kept weakening, substitution and functionality at zero
edits; the positional LR patterns (one pair of branches per induction,
scripted) were the mechanical part.
