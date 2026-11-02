# Layer structures: side conditions by counterexample (issue #48)

Status: **probe done** (2026-10-28), `probes/LayerStructure.v`,
standalone, no axioms (`Print Assumptions` closed for every result
below). The dependent eliminator, condition S3 and the answer for
DeLaM's recursors were added on 2026-11-02 ("The dependent eliminator"
below). The theories are untouched, and the layer-signature refactor of
`compt` (#49) is not started; this note is its input.

The question (issue #48, and the "niche properties and extensions" doc,
items 1 to 3): describe each layer by a tuple of capabilities, and find
by counterexample the side conditions under which a layer structure
supports the metatheory. Then check that the {code, program} × meta-depth
grid, which n-layer DeLaM forms, meets them.

## The toy

STLC with `Nat` and code, every judgment at a layer `j`, over a layer
structure `LS`:

| Field | Meaning | DeLaM |
|---|---|---|
| `ls_le` | what lifts into what | `lle`, V < C < D < M |
| `ls_typeof` | where a layer's types live | `typeof` (C's types are D's) |
| `ls_computes` | β is part of conversion; else equality is static | `compt` |
| `ls_hosts k c` | `Code c` is a type at type layer `k`, with `box` and the analysis | M hosts C |
| `ls_evals j c` | `j` may run `c`-code | `letbox` at M over C |
| `ls_total` | `fix` is not typable | everything total |
| `ls_depth` | meta depth of a type layer | D 0, M 1 |

These are the issue's six capabilities: "computes" and "static or
conversion" are one flag, "whose code it holds" is `typeof` of a code
layer, "where it is analysed" and "hosts `□`" are `ls_hosts`, and
evaluation got a flag of its own, because the results separate it from
analysis.

On code: `box A s` (a closed layer-`c` term `s` of type `A`, tagged with
`A`), the analyses `csize` (the size of the syntax tree) and `cfold` (a
fold with any fixed motive), `run c B t d` (evaluation with a type
conditional: `s` if `t` is `box B s`, else `d`), its fuelled variant
`runk`, and `quote` (axiom 4: `box A s` boxed again, as code one level
up). Typed code `tBox c A`, with `tbox` and `trun`, is the S4 box, which
nothing analyses. `tcast c B t d` is the dependent eliminator of untyped
code into typed code: `tbox s` if `t` is `box B s`, else `d`, under its
own capability `ls_casts`. `cfold`, typed code and `runk` were added for
the question in "Code at its own depth" below, `tcast` for the one in
"The dependent eliminator".

Simplifications against DeLaM, each a place where the result could
change in the real system:
- code is closed: no contextual types, no global context, so `run` is a
  closed `letbox`;
- code is untyped, tagged by its type: `Code c` reads as Σ A. □A, the
  analogue of DeLaM's code of types with `elim_Typ`'s type conditional.
  This is what lets the liar be stated without Löb;
- the folds have a fixed motive. The one dependent eliminator is the
  shallow `tcast`, whose motive is `X ↦ □X` over the type tag; there is
  no structural recursor with a type-family motive (why that is enough
  is in "The dependent eliminator");
- simple types, weak-head call-by-name reduction, and a relation that
  does not mention layers at all.

## Results

Seven side conditions:

| | Condition | Used by | Fails in | Failure |
|---|---|---|---|---|
| S1 | `static_code`: hosted (so analysed) code is static | conversion | `cx_static`: DeLaM with C computing | `csize ⌜(λx. x) 0⌝ ≡ csize ⌜0⌝`, so `4 ≡ 1` at M |
| W1 | `static_down`: nothing computing lifts into a static layer | conversion | `cx_sdown`: DeLaM with D ≤ C | the same, through the lift |
| S2 | `eval_up`: `run` at `j` of `c`-code needs `depth(typeof c) < depth(typeof j)` | normalization | `cx_eval`: the grid with every row running its own code | the liar |
| S3 | `cast_up`: `tcast` at `j` of `c`-code needs `depth(typeof c) < depth(typeof j)` | normalization | `cx_cast`: the grid with every row hosting and casting its own code, `run` strictly upward | the liar through `trun ∘ tcast` |
| W2 | `depth_mono`: lifting never lowers the depth | normalization | `cx_depth`: code of M lifts into code of D (C₁ ≤ C₀) | the liar |
| W3 | `total_down`: nothing partial lifts into a total layer | normalization | `cx_total`: DeLaM with D partial | `fix x. x` at M |
| W4 | `eval_lift`: a layer runs only code that lifts into it | normalization | `cx_lift`: M runs partial C-code that does not lift into M | `run ⌜fix x. x⌝` at M |

Each counterexample structure meets the other six conditions
(`cx_*_others`), fails its own (`cx_*_fails`), and has a closed,
well-typed numeral at a total layer without a normal form, or a
conversion between two distinct numerals.

Under the conditions:
- `normalization` (S2, S3, W2, W3, W4): a closed numeral at a total
  layer evaluates to a literal;
- `conv_sound` (all seven): a conversion between closed numerals at a total
  layer relates two terms with the same literal.

The proof is a fundamental theorem by induction on the meta depth, then
on the derivation (`FT_depth`). The relation itself is not stratified:
code is related when both sides evaluate to one and the same well-typed
`box` (syntactic equality, because `csize` sees syntax). The depth is
used only at `run` and `tcast`: their code's contents were typed at a
lower depth, so the theorem at that depth applies to them. Nothing else looks inside a
`box`.

The liar (`lΩ`) is Lawvere's diagonal: `d := λx. succ (run x (λ_. 0) x)`
applied to its own code reduces to `succ (d ⌜d⌝)`. `run` turns every code
of a function on codes into that function, which is the surjection the
#47 discussion names. It needs `Code c` among the types of `c`'s own
programs, so it needs `c` hosted at its own depth, and it needs `run` of
`c`-code at `c`'s depth.

## Against the four conjectures

1. **Analysed code is static: confirmed**, and with a companion, W1:
   no computing layer lifts into analysed code, which is why the grid
   has no `P_k ≤ C_k'`. Both are needed for conversion only.
   Normalization holds without them.
2. **Analysis is strictly upward: refuted as stated.** A layer may host
   and analyse code of its own depth: the grid with reflexive hosting
   (`grid_gen n true false m`) meets every condition. What must be
   strictly upward is *evaluation* (S2). A second condition appears
   instead: lifting must not lower the depth (W2).
3. **The Layering Restriction: not a separate condition here.** The
   relation does not depend on layers. What is layered is the
   fundamental theorem, which at depth d uses itself below d only, and
   only at `run`. In DeLaM, the relation is defined layer by layer
   because types and universes are layered (`LogRel/Layering.v`). The
   toy has no universe, so it cannot show more than this.
4. **`□` lives strictly above its contents: sufficient, not necessary.**
   It implies S2, since `run` needs `Code c` formable where it runs. It
   can be weakened to S2 plus W2.

Two smaller facts: `ls_le` need not be a preorder (nothing uses
reflexivity or transitivity), and totality needs exactly W3 and W4.

W2's counterexample uses reflexive hosting (code of D hosted at D). With
strictly-upward hosting I expect W2 to be unnecessary: the liar needs
`Code c` among the types of `c`'s contents, and a lift does not move
types. That is argued, not checked. The proof would need another
measure than the layer's depth.

## The grid

`grid_gen n hrefl erefl m`: the cells `V`, `C_k`, `P_k` for every `k`.
`C_k ≤ C_k'`, `C_k ≤ P_k'` and `P_k ≤ P_k'` hold for `k ≤ k'`, and never
`P_k ≤ C_k'`. `typeof C_k = P_k`. `P_k'` hosts `C_k` for `k < k' ≤ n`,
and also for `k = k'` when `hrefl` is set. Evaluation needs a host and a
lift, and is at the same level only when `erefl` is set. Layers are
total below level `m`.

```
depth   code      program
  2     C₂ ─────→ P₂
        ↑   ↖     ↑      P₂ hosts and runs C₁ and C₀
  1     C₁ ─────→ P₁
        ↑   ↖     ↑      P₁ hosts and runs C₀
  0     C₀ ─────→ P₀
          ↖ V, below everything
```

- `grid_good`: the grid meets all seven conditions for every depth `n`,
  every totality bound `m`, and both values of `hrefl`. So it normalizes
  (`grid_normalization`) and its conversion is sound (`grid_conv_sound`).
- **DeLaM is the depth-1 slice.** `emb : V, C, D, M ↦ V, C₀, P₀, P₁`
  preserves and reflects `lle`, and commutes with `typeof`, `compt`,
  hosting, evaluation, totality and depth (`emb_*`); `delam_good`.
  The one depth-1 cell missing from the image is `C₁`, the code of M,
  which nothing hosts (`grid1_C1_unhosted`). So `□□` and axiom 4 are not
  formable in DeLaM.
- **Depth 2** (`grid 2 3`): `□□` is formable at `P₂` (`boxbox`), axiom 4
  is `quote : Code C₀ → Code C₁` (`four_typed`), and T twice runs code of
  code (`eval2_typed`). `eval2 (four ⌜7⌝)` evaluates to `7`
  (`eval2_four`).
- **A partial top level** (`grid n n`: `fix` only at level `n`): every
  lower level still normalizes, by `grid_normalization`, and the top is
  partial (`partial_top`).

## Where the reflexive cell R sits

R, from the Weaver/Löb design (#47), is a program cell whose code is
hosted at R itself (`▷`, analysis only) and run one level up (S4 `□`
with T). In the grid, that is `P_k` hosting its own `C_k` (`hrefl`),
with `C_k` run only from `P_{k+1}`:

```
  1     C₁ ─────→ P₁          P₁ runs C₀ (T one level up)
        ↑   ↖     ↑
  0     C₀ ─────→ P₀ ⟲        P₀ = R hosts C₀ (▷): analysis, no eval
```

- R without T meets every condition (`gridR`, covered by `grid_good`):
  R may analyse its own code (`R_analyses_own_code`), `P₁` runs it
  (`R_runs_below`), and R runs nothing of its own depth
  (`R_no_own_eval`).
- R with T is `cx_eval`, whose liar is the #47 probe's step 2 as a Coq
  term. With untyped code it needs no Löb: the type conditional in `run`
  supplies the diagonal.
- Löb itself (`fix z. M : ▷A`, code that contains itself) is not in this
  toy. It is #47's probe. The finding here is that the grid already has
  a slot for R, and that the boundary #47 draws (no T at R) is the toy's
  S2 exactly.

## Code at its own depth: analysis, evaluation, fuel

What can a layer do with code of its own depth, given that it may not
`run` it? All of the following hold in `gridR` (each program row hosts
its own code), which meets all six conditions, so normalization and
conversion soundness cover them.

- **Fold it, with any fixed motive** (`cfold`, `R_folds_own_code`). The
  fold is structural on the code's syntax and never runs it, so its case
  in the fundamental theorem goes by induction on the code (`R_foldtm`)
  and needs no condition on depth at all. The motive can be `Code c`
  itself, so code-to-code transformations of one's own code are fine:
  rewriting, instrumenting, specializing. That is a partial evaluator's
  shape: it emits residual code and does not run it.
- **Run it when it is typed** (`tBox c A`, `trun`,
  `R_runs_own_typed_code`). Evaluation of typed code at its own depth is
  the S4 box of Davies and Pfenning, and it normalizes: the relation at
  `□A` is the relation at `A` on the contents, structural in the type,
  with no stratification by depth. The only premise is that the code
  lifts into the layer that runs it.
- **Run it with fuel** (`runk`, `fuel_liar_typed`). Running with fuel
  `S n` caps every fuelled run inside the code at `n`. The fundamental
  theorem then goes by induction on the fuel within one depth
  (`FT_depth`). The liar with fuel `n` is typable at R and evaluates to
  `n + 1` (`fuel_liar`): each unfolding is one step of the never-ending
  delay, and the last falls back to the default. This is #47's
  `run : ▷A → Delay A`, cut at `n`.

What it cannot do is evaluate its *untyped* code. That is a theorem, not
only a missing primitive. **`no_own_eval`** (Lawvere's diagonal, Tarski's
undefinability): where a layer hosts its own code, no term `e` of that
layer satisfies `e ⌜f⌝ ⌜f⌝ ≡ f ⌜f⌝` for every `f : Code c → Nat`, even
only up to conversion and only on the diagonal. From such an `e`,
`d := λx. succ (e x x)` has `d ⌜d⌝ ≡ succ (d ⌜d⌝)`, which conversion
soundness refutes. The proof uses only β, `succ` and `conv_sound`, so it
holds of any extension of the analyses that keeps conversion sound:
whatever folds are added, they compute everything about own-level code
except its meaning.

So the line is not "analysis versus evaluation" but **universal code
versus evaluation without a bound**:
- typed code with evaluation at its own depth is safe (S4);
- untyped code (a type conditional on codes, as `run`'s tag test or
  DeLaM's code of types with `elim_Typ` give) with analysis at its own
  depth is safe;
- untyped code with fuelled evaluation at its own depth is safe;
- untyped code with unbounded evaluation at its own depth is the liar
  (`cx_eval`).

The dependent eliminator below adds one line to this list: untyped code
eliminated at its own depth into typed code (or into its own type) is
the liar again.

Implications for Heather's tactics, read off the toy:
- a tactic may inspect, rewrite and specialize tactic code freely;
- it may run its own typed code (S4);
- it may run its own untyped code only with fuel or through a
  `Delay`-valued run;
- it may run untyped code fully only from the level above;
- it may not turn its own untyped code into its own typed code (a
  `tcast` at its own depth), since S4 then runs it.

## The dependent eliminator (2026-11-02)

The question the first round left open: a recursor whose motive is a
type family can take the motive "the meaning of the code", so is it an
evaluator, and is it then safe at its own depth only where that
evaluator is? Checked in the toy with the shallow dependent eliminator
`tcast`, then read off DeLaM's rules for `elim_Typ` and `elim_Trm`.

**In the toy.** `tcast c B t d : □B` for `t : Code c` and `d : □B` is
the dependent eliminator of `Code c` (Σ A. □A) with motive `X ↦ □X`,
read at `B` by the type conditional. Each half is safe at a layer's own
depth: the type conditional alone is what `cfold` already observes, and
`trun` of own-depth typed code is S4. Together they are `run`
(`tcast_hit_is_run`, `tcast_miss_is_run`: `trun (tcast c B t (tbox d))`
and `run c B t d` reduce to the same contents or default).
- **Safe from above (S3).** `cast_up` asks of `tcast` what S2 asks of
  `run`. Under it, `FT_depth` covers `tcast` by the theorem at the lower
  depth, exactly as for `run`, and the grid meets it at every depth,
  with own-depth hosting too (`grid_good`, `R_casts_below`).
- **The liar without it (`cx_cast`).** `gridR 1 2` with `tcast` of each
  row's own code meets the other six conditions, `eval_up` included:
  no layer runs untyped code of its own depth (`cx_cast_no_own_eval`).
  Yet `cd := λx. succ (trun (tcast x (tbox (λ_. 0))) x)` at `C₀` has
  `cd ⌜cd⌝ ⇝ succ (cd ⌜cd⌝)` in three steps, typed at the total layer
  `P₀` (`cx_cast_liar`, `cx_cast_not_normalizing`). So S3 is not
  implied by the other conditions: S2 has to cover every eliminator
  that hands own-depth contents back at their own type, not only `run`.

Why the shallow eliminator is the whole question, in the toy:
- a motive that keeps the contents as code, `X ↦ Code c'`, is constant
  in a simply typed calculus, so its folds are `cfold`, safe at any
  depth;
- a motive that hands them back at their own type, `X ↦ □X` or
  `X ↦ X`, is `tcast` or `run` at the root already; a structural
  recursor adds nothing to the liar, which needs only the root.
- the structural recursor with the meaning motive needs that motive at
  open subterms too: indexed by the subterm's context, `⟦Γ⟧ → A`. This
  is the point at which DeLaM's recursors differ, below.

**In DeLaM: `elim_Typ` at M does not block own-depth hosting.** Read
off the rules (04:1130 to 1300, `Typing/Declarative.v`'s `wf_elimT`,
`wft_gvar`, `wf_gvar` and `Typing/Context.v`'s `lsub_tail`), not checked
in Coq:
1. **The branches cannot use the code's parts as programs.** Every
   branch binds a fresh context variable `g` and the parts as global
   variables over contexts ending in `g` (`U_S : DTyp[g]`,
   `u_t : DTrm[g, x : U_S]`, ...). A global over `Δ` is usable at a
   layer only under a local substitution `δ : Γ → Δ` with
   `lsub_tail δ Δ Γ`: `Γ` and `Δ` end in the same way (04:990). The
   branch's local context extends the recursor's `Γ`, which does not end
   in the fresh `g`. So a branch can box the parts again (code to code),
   but cannot use them as terms or types of M, whatever the motive. In
   the toy's terms, the recursors are folds with code-valued branches:
   `cfold`, never `run`.
2. **No motive is the meaning.** The motive is formed over
   `x_T : CTyp[g] ℓ` with `g` fresh, and the index of a contextual type
   `CTrm[Δ] T` is checked in `Δ` at D (`wft_CTrm`), so no index mentions
   M's local `x_T`. There is no type-level `letbox`. So
   `Σ (x : CTyp[Δ] ℓ). CTrm[Δ] ⟦x⟧`, the toy's `Code c`, is not formable,
   and neither is a motive `x_T ↦ □⟦x_T⟧`, the toy's `tcast`. A motive
   into M's universes, `El (dec x_T)`, decodes the simply typed part of a
   type code into M's universe, but its `El` branch cannot evaluate
   the term code `u_t` (by 1), and the decoded type cannot index code.
3. **The eliminators that do hand contents back are typed.**
   `letbox_Trm` takes `CTrm[Δ] T` to a global of type `T`: the S4 `trun`,
   safe at its own depth. `letbox_Typ` takes a type code to a type
   global, which can index `CTrm` but comes with no term of that type.

So for #49, own-depth hosting (`P_k` hosting `C_k`) may keep `box`,
`letbox_Typ`, `letbox_Trm` and both recursors at `P_k` itself, as long as
the signature's rules keep 1 and 2: branch globals under `lsub_tail`,
contextual indices checked in `Δ` only, and no former that takes a type
code to a type usable as a code index or packages a type code with a
term code of that type (a type-level `letbox`, a Σ of the two, or a type
case into `CTrm`). Adding one of those is S3's case and needs the
strictly upward condition. Two things are not settled by this reading:
at its own depth `C_k`'s syntax contains `P_k`'s own formers, so the
recursors need branches for `CTyp`, `CTrm`, `box` and the recursors
themselves (the argument in 1 is per branch and does not change, but
those rules are not written); and the toy's code is closed and simply
typed, so it does not check 1 and 2 themselves, only that what they
exclude is the danger.

## For the refactor (#49)

The layer signature can be `LS`'s fields with S1, W1, S2, S3, W2 and,
once partiality is wanted, W3 and W4. DeLaM meets them. Before trusting
the list in the dependent setting, three things differ from the toy:
- S2 and S3 must cover every eliminator that hands own-depth contents
  back at their own type. DeLaM's recursors do not ("The dependent
  eliminator", 1 and 2), so own-depth hosting needs no depth condition
  on `elim_Typ` or `elim_Trm`, only that the refactor keeps
  `lsub_tail` on branch globals and contextual indices closed over `Δ`;
- the relation in the theories is layered (`LogRel/Layering.v`), so
  conjecture 3 may come back as a real condition there;
- code there is contextual, with global substitution; the toy's code is
  closed.
