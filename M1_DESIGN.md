# Milestone 1: the MLTT core, normalization through the fundamental theorem

Goal: DeLaM's MLTT fragment (ch. 4 §"Typing and Equivalence Judgments" and
the MLTT computation rules) with a `Prop`-valued Kripke logical relation
(ch. 7 §"Kripke Logical Relations for MLTT", j = prog), proved in
logrel-coq's architecture, up to the fundamental theorem and its immediate
consequences (normalization, canonicity, injectivity of type constructors).

M1 must be in the **final shape**: later milestones add constructors and
rules, not new judgment parameters.

## Fixed now, to avoid a later big-bang

| Choice | M1 decision | Why now |
|---|---|---|
| Judgment shape | `G ; Γ ⊢[i] t : T @ l`. `G` bundles the universe context `L` and the global context `Ψ`, and is unchanged by every MLTT rule. | The paper's judgments carry all four. Adding parameters later touches every file (McTT's S2b experience). |
| Layers | Full `V < C < D < M` with `typeof`. MLTT rules gated as in the paper: V only for variables and conversion; computation (β/η) only at D and M. | Same. |
| Tarski | Separate `ty` / `tm` syntax, `El l t`, type codes in `tm`. | DeLaM is Tarski. Russell was McTT's root problem for `bc_gvar`. |
| Level-annotated judgments | `@ l` on every judgment, level-conversion rule, `Π^{l,l'}`, `λ^{l,l'} x:S.t`, and `app` carrying `l, l', S, T` as in the paper. | Annotations are sub-structure the code-recursion principle needs later. Adding them is a constructor-arity change everywhere. |
| Levels | Syntax `ℓ \| 0 \| 1+l \| l ⊔ l' \| ω`, de Bruijn level variables. Well-formedness means variables < \|L\| and no ω. **Equivalence is semantic: equal under every valuation.** | See below. |
| Global context | `Ψ` is present and syntactically complete (`g : Ctx`, `U : (Δ ⊢ᵢ @l)`, `u : (Δ ⊢ᵢ T @l)`), but M1 only *uses* `g : Ctx`, for contexts ending in `g`. `u^δ`/`U^δ` are in the syntax and have no typing rules yet. | The logical relation's context case and neutral laws already mention them. |
| Syntax | The `spike/Syntax.v` design, extended with the Tarski split and a level sort. Modal formers (`□`, `box`, `letbox`, `CΠ`, `TΠ`, code recursors) arrive later as *additive* constructors. | Tests the spike's "adding constructors is cheap" claim when it matters. |

### Level equivalence

The paper axiomatises `≈` as an idempotent commutative monoid with successor
laws, following Bezem et al., and notes it is decidable. M1 *defines* `l ≈ l'`
as equality of evaluations under all valuations of the level variables, and
the order by the same means. This is the intended model. It makes every
algebraic rule a lemma, keeps typing proofs free of level algebra, and gives
the logical relation a well-founded measure: evaluation with all variables at
0. A decision procedure (normal forms) is only needed by the checker, a later
milestone.

## Deliberately NOT in M1

- Kripke quantification over *global* and *universe* weakenings. The paper's
  weakening triple is ψ = (θ, γ, τ). M1's relation is Kripke in local
  weakenings only: renamings `r` with `wkr r Δ Γ` (`Typing/Properties.v`).
  Adding θ/γ changes the Kripke quantifier in `LRpi`/`PiRel` and the
  weakening lemmas, not the other cases.
- `UΠ` / level binders and ω's semantics (checked in the universe spike).
- The algorithmic instance and checkers.
- Layers C and V in the fundamental theorem: M1 proves it for the computing
  layers `i ∈ {D, M}`. MLTT derivations at those layers never leave the layer.

## Module plan (logrel-coq counterpart in brackets)

1. `Syntax/`: `Level` (syntax, evaluation, `≈`, `<`), `Term` (spike + Tarski),
   `Subst` (the spike's laws), `NormalForms` (whnf / whne for types and
   terms), `Reduction` (untyped weak-head reduction), `Commute`
   (per-constructor push equations and commutation lemmas), `Weakening`
   (order-preserving embeddings). [`Syntax/*`, `AutoSubst/*`]
2. `Typing/`: `Context` (layers, `gctx`, lookup), `Declarative` (the
   judgments, `Prop`), `Properties` (context extraction, weakening),
   `TypedRed`, `Generic` (the paper's four generic equivalences plus the
   laws of §7.1), then `DeclInstance`.
   [`DeclarativeTyping`, `GenericTyping`, `TypingProperties/*`,
   `DeclarativeInstance`]
3. `LogRel/`: `Def` (all cases in one inductive), `Escape`, `Basics`
   (stages, level conversion), then Irrelevance, Symmetry, Transitivity,
   Weakening, Neutral, Reduction. [`LogicalRelation/*`]
3. `Validity/` and `Fundamental`. [`Validity/*`, `Fundamental`]
5. `Consequences`: normalization, canonicity, Π/U injectivity.
   [`LogRelConsequences`]

## Process

- Green build at every checkpoint; commit per module.
- Proofs use named hypotheses and shape-matching, not positional selectors
  (inversion naming shifts whenever a constructor is added).
- No global hint-DB search in hot proofs. Build time is tracked per module.

## Deviations from the paper (all admissible or harmless)

- (M7 C1b) The abstractions of the meta level carry the former they
  introduce: `ulam n l T t`, `clam l T t`, `tlam Δ l l' T t`. The paper's
  are unannotated. This makes type checking decidable for all terms; a
  paper term is typed iff some annotation of it is (the rules choose the
  body type the annotation records). See `M7_DESIGN.md` C1b.

- **Level equivalence is semantic** (see above).
- **Reduction ignores annotations** (`Syntax/Reduction.v`). The paper's
  redexes repeat annotations (`El (l⊔l') (Π^{l,l'} …)`,
  `app (λ^{l,l'} x:S. t) l l' S …`). Typing fixes them only up to `≈` and
  conversion, so syntactic matching would leave well-typed redexes stuck.
- **Typed reduction includes its equation** (`Typing/TypedRed.v`), as in
  logrel-coq: `[T ⤳* W]` = source typed, untyped reduction, and `T ≅ W`.
  The paper uses typing plus untyped reduction and proves soundness via
  preservation. Its β case silently needs Π-injectivity, which only comes
  from the logical relation.
- **Explicit reflexivity rules** and some extra well-formedness premises on
  congruences (as in logrel-coq).
- **The logical relation is staged by the level measure** (`LogRel/Def.v`).
  Π relates its domain at a level not strictly below its own, so levels
  can't be the recursion index. Stage `n` is one inductive over all levels,
  and only the universe case refers to earlier stages. `LogRel l` uses stage
  `lmeasure l`; `cumul_up`/`cumul_down` relate stages. Level equivalences are
  folded into each case, so the paper's level-conversion case is a lemma
  (`LR_lconv`).
- **Term relations depend on both sides' types** (the paper's symmetric
  presentation: `NeRel V V'`, `PiRel … A B A' B'`, duplicated premises).
  Irrelevance (`LR_irrel`: same left type, any right types) goes through
  conversion.
- **Saturation** (`LogRel/Def.v`). Every case accepts any term relation
  `R` with `releq R canonical`. Symmetry must build the Π derivation with
  the flipped domain relation, but the induction hypothesis only yields
  `∃R', … ∧ R' ⇔ flip domR`, and a `Prop` existential can't be turned into
  a function. Saturation makes `flip domR` itself acceptable
  (`LR_releq`). This replaces the crux spike's canon/packs (propext +
  funext): **the logical relation's metatheory is axiom-free so far.**
- **The universe case is indexed by the level read off the left type's
  normal form** (`URel rec G Γ l1` for `T ⤳* U l1`), so two derivations for
  the same left type have literally the same relation.
- **`URel` quantifies over equivalent `El` annotations**: decodings
  `El la w` / `El lb w'` are related for all `la, lb ≈ l`. This is the same
  device as the paper's application annotations in the Π case. It makes
  symmetry and level conversion of the universe case go through, since
  otherwise they need an "annotation irrelevance" for `El`. The fundamental
  theorem can provide it, because `El` reduction ignores annotations.
- **`LRpi` records the generic equality of domains and codomains**
  (`A ≈ A'`, and `B ≈ B'` under the left domain) instead of the whole Π
  types (derivable by `geq_ty_pi`). Needed by irrelevance and
  transitivity, which otherwise need Π-injectivity of the generic
  equivalence.
- **Generic laws include context conversion** of the last entry (with a
  level change), as the paper uses in right irrelevance. The declarative
  instance gets it from stability.
- **Syntactic metatheory before the relation** (as in the paper's ch. 5,
  unlike logrel-coq): substitution, stability, functionality and
  presupposition are proved directly for the declarative system, for layers
  with `typeof i = i`. Typed local substitutions are defined extensionally,
  by lookups, and carry `LK nftm d` (normal forms of the entries) for the
  identity laws.

## Status (2026-09-24, end of session 3): M1 complete

About 6.3k lines, 32 files, **no admits, no axioms** (every theorem prints
"Closed under the global context"). A clean build takes about 23 s; no file
takes more than 4 s.

The fundamental theorem (`Validity/Fundamental.v`) holds for every
`GenericEqLaws` instance, and the consequences are proved generically and
then for the declarative instance at any computing layer.

| File | Contents |
|---|---|
| `Syntax/Level.v` | levels, semantic `≈`/`<`, algebraic rules as lemmas, measure |
| `Syntax/Term.v` | Tarski `ty`/`tm`, `ctx`, `lsub`; local renaming and substitution; `lsingle`, `lsingle2`, `lsucc` |
| `Syntax/Subst.v` | the substitution algebra (spike laws for three sorts) |
| `Syntax/NormalForms.v`, `Reduction.v` | whnf/whne; annotation-agnostic weak-head reduction, determinacy, renaming stability |
| `Syntax/Commute.v` | `push_ren`/`push_subst` constructor equations; commutations for single substitutions; renaming outputs are normal |
| `Syntax/SubstCommute.v` | substitution preserves normal forms; an arbitrary substitution commutes with the rules' own substitutions |
| `Syntax/Weakening.v` | OPE data `wk`, `wk_wf`, composition |
| `Typing/Context.v` | layers + `typeof`/`compt`, `gdecl`/`gctx`, `in_ctx` |
| `Typing/Declarative.v` | the six mutual judgments with layer gating; `typing_mut` scheme |
| `Typing/Properties.v` | `ctx_extract` (all layers); `wkr` renaming-weakenings; `weakening_r` for `typeof i = i` |
| `Typing/Substitution.v` | typed terms are normal (`typed_nf`); typed local substitutions `[Δ ⊢ d : Γ]` by lookups; `substitution` |
| `Typing/Functionality.v` | single substitutions; stability (`stab_*`, last entry, with level change); `functionality` |
| `Typing/Presupposition.v` | `presupposition` + named corollaries (`wf_tm_ty`, `eqty_wf_l/r`, `eqtm_wf_l/r/ty`) |
| `Typing/TypedRed.v` | `tyred`/`tmred`, refl/trans/conv/lconv, weakening, whnf determinacy |
| `Typing/Generic.v` | `GenericEq` (fixed computing layer) + `GenericEqLaws` (incl. context conversion) |
| `Typing/DeclInstance.v` | `DeclEq i Hi` / `DeclEqLaws`: the declarative instance at a computing layer `i` |
| `LogRel/Def.v` | `releq`, `NatRel`/`NatNf`, `URel`, `NeRel`, `PiRel`, staged saturated `LR`, `LogRel` |
| `LogRel/Escape.v` | `escape_ty`, `escape_tm`; conversion helpers |
| `LogRel/Basics.v` | `cumul_up`, `cumul_down`, `LogRel_stage`, `LR_releq`, `LR_lconv` |
| `LogRel/Irrelevance.v` | `LR_irrel` (right irrelevance, as `releq`); inversion by the left normal form (`LR_inv_nat/U/ne/pi`) |
| `LogRel/Symmetry.v` | `LR_sym` (`flipR`), by strong induction on the stage |
| `LogRel/Transitivity.v` | `LR_irrel_left`, `LR_trans`, `LR_refl_l/r`, `LR_tm_refl_l` |
| `LogRel/Weakening.v`, `Neutral.v`, `Reduction.v` | `LR_wk` (Kripke index = OPE data, composable via `wk_comp`), `LR_neutral`, `LR_red_ty`/`LR_red_tm` |
| File | Contents |
|---|---|
| `Validity/Def.v` | `LRrel` (canonical relation = union over derivations, via irrelevance + saturation; plays the spike's "canon" role without axioms), `SubRel` (by recursion on `Γ`), `VTy`, `VTm`; `SubRel` is a Kripke PER giving typed substitutions |
| `Validity/Props.v` | stages, irrelevance/level conversion of `LRtm`, `VTy`/`VTm` PER + `VTm_conv`, `SubRel_cons`, `SubRel_lift` (var 0 by neutral reflection) |
| `Validity/Basic.v` | variables, `Nat`, `zero`, `succ`, `U`, `El`, codes of `Nat`/`U`, `Nat ≅ El 0 ⌜Nat⌝`, `U ≅ El (1+l) ⌜U⌝` |
| `Validity/Pi.v` | `LR_pi_here` / `V_pi` (domain/codomain relations `piDom`/`piCod` = `LRrel`) |
| `Validity/Red.v` | typed app congruence, β through equivalent annotations |
| `Validity/App.v`, `Lam.v`, `PiComp.v` | application, λ, `funext_K` (extensionality from the Kripke clause), β, η |
| `Validity/Natrec.v` | `natrec_core` (by `NatRel_mut`: reduce to normal forms and move the types with `LRtm_conv_l/r`; zero/succ by anti-reduction; neutrals by `LR_neutral` + `gne_tm_natrec`), `V_natrec`, `V_natrec_zero`, `V_natrec_succ` (anti-reduction on the left only, `LRtm_red_l`) |
| `Validity/CodePi.v` | `tyred_El_pi` (decoding a Π code, with annotations up to `≈`), `V_code_pi`, `V_El_pi` (both via `LR_pi_here` with `V_El` of the component codes) |
| `Validity/Fundamental.v` | rule-shaped wrappers `ft_*` (derive the validity lemmas' extra typing premises by presupposition and stability); `fundamental` by `typing_mut` with motive `i = ge_layer -> V…`; each case closed by the first lemma that applies (`ft_case`), so no dependence on constructor order |
| `Validity/Consequences.v` | `SubRel_id`; `reducible_ty/tm/eqty/eqtm`; `nat_canonicity`; `pi_inj`, `U_inj`; `whnf_normalization_ty/tm`; `no_closed_neutral`, `closed_nat_canonicity` (closed naturals are equal to numerals); `nat_not_pi`, `nat_not_U`, `U_not_pi` |
| `Validity/DeclConsequences.v` | the same for the declarative system at a computing layer `i` (`decl_*`) |

Notes on the final interfaces:
- `V_natrec` takes the right-hand typing premises at the right annotation
  `l'`; `ft_natrec_eq` derives them (presupposition, `stab_tm` with a level
  change, `eqty_single`, `lsub_wf_lsucc`).
- `V_code_pi` takes `s ≅ s'` declaratively (the FT has it; `wf_code_pi` uses
  reflexivity), to move `t'` into the context `Γ, El l3 s'`.
- `closed_nat_canonicity` needs only an empty *local* context: M1 has no
  typing rule for global variables, so every typed neutral has a local
  variable at its head (`no_closed_neutral`). **Revisit in M2**, when
  `u^δ` becomes typable: closed canonicity will then need an empty global
  context too.

## Next steps

M1 polish is done (closed canonicity, discrimination of `Nat`/Π/`U`). Deep
normalization (full normal forms) is deferred: M2 doesn't need it, and it
belongs with the algorithmic instance, which is also deferred. Next is M2,
the modal core (see `M2_DESIGN.md` once written).

## Proof-engineering gotchas (learned the hard way)

- `constructor` on a declarative equality goal happily applies a generic
  rule (`eqty_sym`, `eqtm_conv`, …: always unifiable; since the 2026-09-29
  perf pass they are the judgments' last constructors, so a plain
  `constructor` commits to a wrong congruence first). Apply the intended
  rule by name. Since
  saturation, the same holds for `LR`: every constructor's conclusion is
  `LR … R` with `R` a variable, so `econstructor` always picks `LRnat`.
- Section-local lemmas with explicit section hypotheses (`Hi`, `Hv`) keep
  only the ones they use, so their arity varies. Pass arguments by name
  (`(lemma (x := …))`) or with `eapply … ; eassumption`.
- `match goal with IH : _ |- _ => exact (IH …) end`: an ill-typed
  application raises an error that `match` doesn't backtrack on. Filter the
  hypothesis by shape first (`IH : _ = _ -> _`) or use `eapply`.
- A section `Context` hypothesis about the indices (e.g. `H : LR … T …`)
  blocks `destruct H` from substituting into other hypotheses. `revert`
  them first (see `LR_inv_*`).
- Avoid broad `Hint Extern` on `eq_ty (subst _ _) (subst _ _)`-like goals.
  One such hint made `Functionality.v` search for over 100 s. Prefer
  per-case manual steps with pre-asserted facts.
- Probe goals in a scratch file under the session scratchpad:
  `coqc -Q theories DeLaM file.v` inside `nix develop`, with `Show.` before
  `Admitted.`
- **Never `cbn` the mutual substitution fixpoints.** It exposes raw `fix`
  bodies. Use `push_ren`/`push_subst` (rewriting with per-constructor
  equations in notation form), then the commutation lemmas (`wk_rewrite`
  in `Typing/Properties.v`).
- Notation-form (`x⟨r⟩`, `x[d]`) and raw (`ren_ty x r`) forms are
  convertible but not syntactically equal. State lemmas in notation form;
  `fold_subst` folds back if raw forms appear.
- Annotate the sort in lemma statements (`(T : ty)`): typeclass resolution
  otherwise picks an arbitrary instance.
- Weakening proofs quantify over renamings satisfying `wkr`, not `wk` data:
  `eauto` cannot invert `wk_ren ?ρ = rlift …`.
- `repeat split` also splits single-constructor `Prop` records (`tyred`,
  `tmred`). Use explicit `conj` chains.
- `eauto` does not unfold definitions like `reds`; unfold first.
- Apply `LRU`/`LRpi` with explicit level arguments; otherwise levels not in
  the conclusion stay as evars.
- `Definition` cannot be a module or section name.
- Induction on the mutual judgments leaves hypotheses named `H`, `H0`, ….
  Select IHs by shape (`match goal with IH : _ |- LR … => eapply IH`), never
  by number.
- Per-case constructor search (`wk_step` in `Typing/Properties.v`, trying
  each constructor under `solve`) is robust and fast. Use it instead of
  `econstructor`, which commits to the first unifying constructor.

### Build-time gotchas (2026-09-29 perf pass, clean build 513 s → 168 s)

Each of these cost tens of seconds, and each grows with the number of
formers, so it gets worse with every extension:

- **Quadratic case splits.** `destruct c; try destruct T` (or
  `destruct t, t'`) makes one goal per pair of formers. Destruct the second
  only where it is read: `redt_case T` (`Syntax/Recursor.v`) for `redt`'s
  index, and `leq_cases` for `≡ₗ`, which closes mismatched formers with
  `exact (False_ind _ H)` before running `cbn` on the one that survives.
- **A failing `apply`/`eapply` of a specific lemma tried on every case**
  (`try solve [apply elimT_lwf; …]` in a `typing_mut` proof) unfolds the
  lemma's conclusion against every former: 80 s in `StaticCode`. Guard it
  with a syntactic `lazymatch goal with |- tm_lwf _ (elimT …) => …`. Match
  the head of the *conclusion*, with the right arity (`EP EM` count);
  `|- context [x]` also sees the judgment's context.
- **Dispatcher order.** A `first [...]` whose early alternatives apply to any
  goal (sym, trans, conv, `eauto` with an evar middle) pays their failure on
  every goal. Put the former-specific rules first (`f_ty`, `m_ty`), the
  manual cases before `any_rule` (`GWeakening`, `GSubstitution`), and
  `cbn`-based side solvers last (`br_tac`). The same holds for the
  constructor order of the typing judgments, which `econstructor` follows:
  the generic rules (refl, sym, trans, conv, lconv, leq) come last in
  `Declarative.v`; keep new generic rules there.
- **Push tactics are generated.** `push_ren`, `push_subst`, `push_gren`,
  `push_gsubst`, `push_gwa`, `s_push`, `gl_push`, `us_rw_all` (in
  `us_rewrite_all`) find an `OP (C …)` subterm
  syntactically and rewrite with `C`'s lemma (a head table). The old
  `repeat progress (rewrite ?l1, …, ?ln)` cost one traversal of the goal
  per lemma per pass, 3–5 s per metatheory proof. A new former's push
  lemma goes into the table: regenerate it with `tools/gen_push.py` (usage
  in its header), or add the arm by hand; a missing arm leaves the push
  undone, which shows as a failing case. Table heads are written `@h`
  (a bare class method in a pattern gets its implicit arguments). A lemma
  stated on a sort's fixpoint (`subst_ty`) is also filed under the class
  method goals use (`@subst`): the generator's `ALIAS` table.
- **`eauto` depth.** Failing searches dominate: `eauto 3` then a final
  `eauto 4` on the leftovers cost a third of `eauto 4` up front
  (`Presupposition`).
- **Raw fixpoints left by `cbn`** (2026-10-04 pass). `cbn [gren_tm]` on a
  recursor's scrutinee can leave its arguments as the raw mutual block,
  `(fix gren_ty … for gren_ty) A ξ`, instead of `gren_ty A ξ`. Every later
  `rewrite` motive then carries the block, and `Qed` re-checks it: 20 s in
  `redt_gren`. `fold gren_ty gren_tm` after the `cbn` (`gpeel_push`,
  both copies). A `Qed` much slower than its tactics is the symptom.
- **`injection` on a big constructor term.** `injection` on two `mkrb`
  blocks unfolds the whole bundle (6 s, and 4 s more at `Qed`). Prove the
  injectivity once by projections (`mkrb_inj` through `tup_nth`) or on
  variables (`elimT_inj`), and use the lemma.
- **Refuting a head by `inversion`.** `inversion Hn` for `Hn : whne v`
  with `v` a value cost a third of `AlgDec`; `discriminate (whne_ne_head
  Hn)` decides it by computing `ne_head` (`AlgPER`).
- **Normalising side conditions.** `cbn; exact I` normalised the whole
  bundle for every `hd_ok` side condition of a `rewrite ?motT_subst`;
  `exact I` alone converts lazily (`hd_tac` tries it first).
- **Definitions unfolded by failing unification.** In a fundamental
  theorem's dispatcher, a failed `eassumption` against `VTyS …` hypotheses
  retries with both sides unfolded. `Local Opaque VTyS VTmS VCtxS VCtxEqS`
  around the theorem took `FundamentalS`'s cases from 19 s to 6 s.
- **A failing search under binders.** `apply wnf_sup; eauto` spent 16 s in
  the one premise it could not solve (a `forall ρ` with ten binders); guard
  `eauto` by the goal's shape. A dispatcher's applies are the same story
  as above: `leq_go` (`LevelRed`) picks its peeling lemma by the goal's
  head (136 s → 28 s).
- **The same quadratic split, hidden in a helper** (2026-10-11 pass).
  `destruct x; cbn in E` (AlgStruct's `lstep`) or
  `destruct x; cbn; dec_solve` (LevelDec's `leq_dec_all`) runs `cbn` on
  every mismatched former too. Close those by conversion first:
  `try exact (False_ind _ E)`, or `try exact dec_False` for a `Dec`
  goal (62 s → 3 s, 51 s → 9 s). Each mismatched goal still costs
  about a millisecond in a big context, so a lemma that splits two
  arguments stays a few seconds; `try contradiction` costs 40 times
  that and `exact (match E with end)` 100 times.
- **A file waiting for laws it does not use.** `NormalForms` needed only
  the definition of `≡ₗ`, yet waited for `LevelEq`'s 78 s of laws, and
  everything after it waited too. The definitions are now `LevelEqDef`;
  `tools/imports.py` lists files whose `.glob` references end well
  before what they require. Split such a file rather than speed it up.
- **Raw fixpoints before `f_equal`.** After `cbn [ren_ty ren_tm …]`,
  `repeat f_equal` on goals holding `fix ren_ty …` blocks took 12 s
  (`tmNth_ren`); `fold ren_ty ren_tm` first, 0.3 s.
- **`injection`/`inversion` on `Some r = Some r'`** with a big unfolded
  reduct copies the reduct into the projection's default value:
  `apply Some_inj in E` (`Syntax/Recursor.v`) instead.
- **Pointwise proofs of shifted leaves.** `(T⟨↑⟩⟨↑⟩)[llift (lsingle c)]
  = T⟨↑⟩` by `subst_comp`/`subst_ext` and one case per variable cost
  75 s in `nth_reds_succ`; `shift_cancel` (`SubstCommute`) rewrites
  such leaves directly (shift past a lift, cancel against a single
  substitution). Its side conditions need `nfty T` for an unshifted `T`.
- **`now`/`easy` in a big context.** `now apply lequiv_sym` spent 6.6 s
  on `lequiv l l` (`easy` walks every hypothesis); close it by the
  lemma you mean. Likewise `intuition` inside a `Hint Extern` runs on
  every search node: the `lwf` hint in `Presupposition` uses
  `repeat split` instead.
- **One typing, many proofs.** `elim_Wf`'s branch scope was typed by
  `wtop` inside `brΓ_conv` (22 s, critical path) and again in `RecAdm`;
  `br50_scope` (`Typing/WfScope.v`, off the path) types it once.
- Measure before guessing (see `CLAUDE.md`, Build, for the tools):
  `tools/build-profile` for a timed build and its report,
  `tools/proofs.py` for the slowest proofs (tactics vs `Qed`),
  `tools/ltacprof.py FILE LINE` for one proof's Ltac profile and
  sentence times; `time "tag" tac` per goal separates the cost of
  successes from failures.
