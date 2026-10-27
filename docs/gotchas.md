# Proof-engineering gotchas

Learned the hard way, from M1 on (first collected in M1's design notes,
`docs/design/M1_DESIGN.md`). Check new proofs against them; the
milestone design docs record further gotchas met per former.

## Proof engineering

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
- `destruct` on a constructor-indexed hypothesis (`whnf w`, `whne w`, …)
  introduces the constructor's fields under the binder names of its
  declaration (`whnf_corec l l' li X A B C k Y c j y` brings an `X`). A
  later `pose proof … as X` then fails because `X` is taken, and inside
  `first [ … ]` that shows only as "No applicable tactic". Name such facts
  so that no constructor's binder can clash (`Xc` in `Canonicity.v`'s
  `value_canon`), or use `as ?X`.
- `kwk` has primitive projections (`M18_DESIGN.md` "Associative
  worlds"), and `cbn [ … ]` reduces a primitive projection of a record
  only when the projection is in its list. `kw_γ`/`kw_r` are definitions
  over `kw_gk`/`kw_rk`, so `cbn [kw_γ kw_r]` alone unfolds them, gets
  stuck on `kw_gk {| … |}` and folds back, silently. List `kw_gk kw_rk`
  as well (and `kw_mk` for a world it builds). At a composite world,
  rewrite with `kw_γ_comp`/`kw_r_comp` instead of a `cbn`.

## Build-time gotchas (2026-09-29 perf pass, clean build 513 s → 168 s)

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
  `change (gren_tm ?x ?ξ) with x⟪ξ⟫` does not catch the block: M18b's
  and M17's push lemmas (`gren_mOutCorec`, `gs_tmDNth`, …) spent 12 to
  24 s each in `Qed` until their loops ran `fold` after the `cbn` (#60).
  The same block appears under a former whose argument `cbn` cannot
  reduce (M17c: `gsubst_ty (tyEl l (usubst_tm x⟨↑⟩ φ)) σ`, a weakened
  payload in a declared type), and then no commutation lemma matches.
  Push the substitutions through the former by its equation first
  (`us_El_raw`, `gs_DVec_raw` in `gs_norm`, RecSBase), then commute them
  past the weakening (`usubst_ren'`, `grs_tm_raw`), and `cbn` last.
- **`f_equal` on a wide constructor.** `f_equal` tries to close each
  argument's equation by conversion, which unfolds the operations on
  both sides when they differ (`uren_tm A ρ = uren_tm A ρ'`): 3.5 s for
  one `corec` or `elim_IWf` case (twelve arguments) of a syntax-wide
  law, so every `*_all` law of `Subst`, `GSubst` and `Universe` doubled
  with M18b. `cong_spine` (`Subst`) peels the application spine with
  `f_equal2` and closes only syntactically equal arguments: those three
  files went from 114 s to about 50 s (#60). Use it in place of
  `f_equal` in a syntax-wide induction.
- **One law per pass in a rewriting loop.** `repeat first [cbn …
  | rewrite L1 | … | rewrite L9]` fails every earlier law before the one
  that applies, and each failed `rewrite` traverses the whole term
  (`mOutCorec_ren`'s push: 12 s). One pass of `cbn …; rewrite ?L1, …,
  ?L9` under `repeat progress` makes as many passes as the term is deep
  (3 s). The same holds for a congruence step that tries a rewriting
  tactic before `f_equal` on goals it cannot close (`mcong`, 16 s → 4 s).
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
  A lemma tried by `apply` on every leftover goal of a mutual induction
  is the same: `apply dnf_mOutCorec` unified `mOutCorec` (simpl never,
  but still δ-unfoldable) with twenty other goals' terms, up to 12 s
  each; `typed_dnf` went from 89 s to 26 s once it ran under a
  `lazymatch` on the goal's head (#60).
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
  `apply Some_inj in E` (`Syntax/Recursor.v`) instead. Each new
  former's reduct grows the cost in every `redt` lemma still using
  `injection`: `elim_IWf`'s cost `redt_ren` and `redt_usubst` 130 s
  each until they moved to `Some_inj` (2026-10-14).
- **A bare `split` in a repeated peeler** hnf's every goal that is not
  yet a conjunction, unfolding definitions to look for one: 71% of
  `gfree_redt` (510 s for `Unfold`). Split only `|- _ /\ _` (a
  `lazymatch`), and add a last `progress hnf` alternative for the goals
  that needed it (2026-10-14, `gf_peel`, `dnf_redt`).
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
- **A chain of `Require`s is a chain of the build** (2026-10-12 pass).
  Files that each required the previous one (the Validity per-former
  files, `Generic` after `StaticCode`, `AlgPrereq` after the whole of
  `FundamentalM`) ran one after another although most used only a
  common base; and a file whose proofs are independent syntax
  inductions (`LevelEq`'s laws, `AlgDec`'s cases) ran them in sequence.
  `tools/depgraph.py` finds both (the latest module each declaration
  needs; the longest chain of declarations using one another).
  Requiring what is used and splitting such files took the critical
  path from 853 s to 687 s (903 s → 748 s wall at -j4).
- **A section split across files** (`RecS*`, 2026-10-12). A section
  cannot be reopened in another file, so `RecS`'s per-former lemmas,
  each independent of the others, ran in one 100 s file. Its hypotheses are now
  one class (`RecH.RecHyps`, over the data), and each file reopens a
  section of the same name over the same implicit data, takes the
  instance `{RH : RecHyps …}` and declares every hypothesis as a `Let`
  of its field: statements, proofs and `Proof using` lines are
  unchanged, and a lemma from another file, applied without its
  section arguments, finds them by instance resolution of `RH`. What
  this needs: every section variable implicit (`Context {EP EM …}`);
  `Ltac`s defined in a section vanish at its `End`, so the shared ones
  live outside it and name a hypothesis by its projection
  (`RecH.He`); a definition that uses data but no hypothesis (`RT`,
  `Rt`) cannot infer its data, so the files using it bind it to theirs
  with a `Local Notation`; and an argument proved by `ltac:(…)` may be
  elaborated before `RH` is found, so pass `(RH := RH)` there.
  The split (a base, eight parts, the recursion) took the RecS chain
  from 100 s to 47 s and the critical path from 693 s to 634 s (743 s
  → 713 s wall at -j4, back to back; total CPU +25 s for the parts'
  repeated loading).
- **Syntax waiting for typing** (2026-10-12, Typing metatheory). Each
  metatheory file on the critical path (`Reduction`, `GWeakening`,
  `Substitution`, `Presupposition`, `WfNth`) began with lemmas that need
  no typing, or only an earlier part of it: the recursors' data and
  reducts under renaming or substitution, the `push_gren` table,
  reduction under global renaming, `nth`'s untyped reductions,
  `presupposition`'s per-former lemmas (which need `Functionality`, not
  the global substitution chain after it). Moved verbatim into
  `ReductionBase`, `GRenRec`, `SubstRec`, `WfNthReds` and `PresupAux`,
  which the old files export, they build beside the chain: critical path
  482 s → 412 s, wall 546 s → 473 s at -j4 (statements checked
  identical with `Check` under `Set Printing All`). `depgraph.py`
  counts every declaration after an `Ltac` or hint as using it, so it
  marks such lemmas as needing the latest module; `--decls` shows them,
  and compiling the moved part against a trimmed `Require` settles it.
  A lemma left behind in a section that is now split (`pre_gvar_ty` and
  its kin need `GSubstitution`) reopens a section over the same
  variables and passes them to the moved lemmas explicitly
  (`lle_D_i Hi Hv`).
- **A derivation needed before its metatheory** (2026-10-15, `dnth` in
  `RecWf`). An early file typing a derived former by unfolding it
  re-proves the derivation in every instance; instead, state the
  derivation once with the metatheory it uses as premises
  (`DNthCore`: the family's instances under weakenings, bounded by the
  depth the derivation reaches), discharge them by the metatheory where
  it exists (`DNth`) and by the automation at concrete instances where
  it does not (`RecWf`). An automation whose one case needs a late file
  calls it through an `Ltac` hook (`Ltac wdnth := fail …` in the early
  file, `Ltac wdnth ::= …` in the late one), so only the lemmas using
  that case wait for it (`RecWfBase`/`RecWf`).
- **One proof, one core** (2026-10-27). A mutual induction over the
  judgments is one proof, and a file-level build cannot split it: the
  typing inductions held 322 s of the critical path on one core. Run the
  case tactic under `par:`, which checks each goal in a worker process
  (`-async-proofs-tac-j` in `_CoqProject`, 3 workers):
  `apply typing_mut; intros. par: ((T0); (T1); …; (Tn)).` for what was
  `apply typing_mut; intros; T0. all: T1. … all: Tn.` (`weakening_all`
  56 s → about 25 s). Each `all:` stage goes in its own parentheses: in
  `T0; split; [a | b]` a goal that `T0` closes leaves the dispatch with
  no goals, which fails ("expected 0 tactics"), while `T0; (split; [a |
  b])` runs the stage per goal. `par:` needs the tactic to close each
  goal or leave it untouched, and goals without evars, so a proof that
  ends in positional selectors or bullets (`Functionality`,
  `GStatic.equiv_gsubst`) stays as it was; so does lemma-level
  parallelism, `coqc -async-proofs on`, which made `RulesS` twice as
  slow. The same applies to a `br_all` table proof (`brRes_wf`,
  `brΓ_conv`).
- **`Print Assumptions` walks every proof term below it**: 30 s each
  for the consequences at the end of the build, where nothing ran
  beside them. They are in `checks/Assumptions.v`, run by `make
  assumptions`, not by `make`; add a new main result there.
- **Computing, not `cbn`-ing, a fact about concrete data.**
  `closed_brDecls` ran `cbn` over each of the 60 branch scopes to see
  that a global substitution under their binders leaves them alone:
  88 s on the critical path, rebuilding the `nth`/`dnth` telescopes
  symbolically. `vm_compute` decides each one at an abstract
  substitution in milliseconds (0.2 s in all). When the data is
  concrete and the goal an equation that holds by computation, try
  `vm_compute; reflexivity` first.
- **Substitution equations over opaque atoms: compute on a template**
  (2026-10-27). `dnth`'s motive equations (`F⟨rlift ↑⟩…[lsingle (…
  n⟨↑⟩ …)] = …`) were proved by rewriting lookups pointwise: 17 of them
  took 48 s of `dnth_step_wf`, in ~30k `rewrite`s. `TemplateEq.geq`
  puts global variables for `F` and `n`, where the operations compute,
  proves that equation by `vm_compute`, and substitutes `F` and `n`
  back by the commutation laws of global substitution: 6 s for the
  lemma. Two traps: an atom left as a Coq variable gets `lcons'`'s
  match stuck, and `vm_compute` reads a stuck match back with every
  branch normalized (210 s for one goal; `geq` checks first), and a
  failing `exact` of a near-miss falls to conversion, which unfolds the
  operations on the atoms (40 s; `geq` compares syntactically first).
- **`cbn` where `cbv` would do, and `cbn; lia` on a judgment**
  (2026-10-27). `wnorm` normalised the branch scopes' typings with
  `cbn [...]`; their terms are closed up to global variables, so
  `cbv beta iota zeta delta [...]` (same list) computes the same normal
  form without `cbn`'s refolding: `RecAdm` 160 s → 88 s, `WfScope`
  50 s → 23 s, `AlgPrereq` 62 s → 35 s, with `br_side` no longer trying
  `solve [cbn; lia]` on typing judgments (a third of `brRes_wf`). `cbv`
  leaves a raw `fix` where an operation is stuck on a variable, so it is
  for closed data only.
- Measure before guessing (see `CLAUDE.md`, Build, for the tools):
  `tools/build-profile` for a timed build and its report,
  `tools/proofs.py` for the slowest proofs (tactics vs `Qed`),
  `tools/ltacprof.py FILE LINE` for one proof's Ltac profile and
  sentence times; `time "tag" tac` per goal separates the cost of
  successes from failures.
