# Layer structures: side conditions by counterexample (issue #48)

Status: **probe done** (2026-10-28), `probes/LayerStructure.v`,
standalone, no axioms (`Print Assumptions` closed for every result
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
`A`), the analysis `csize` (a fold with a fixed motive: the size of the
syntax tree), `run c B t d` (evaluation with a type conditional: `s` if
`t` is `box B s`, else `d`), and `quote` (axiom 4: `box A s` boxed again,
as code one level up).

Simplifications against DeLaM, each a place where the result could
change in the real system:
- code is closed: no contextual types, no global context, so `run` is a
  closed `letbox`;
- code is untyped, tagged by its type: `Code c` reads as Σ A. □A, the
  analogue of DeLaM's code of types with `elim_Typ`'s type conditional.
  This is what lets the liar be stated without Löb;
- the analysis has a fixed motive, so it cannot decode code into a type;
- simple types, weak-head call-by-name reduction, and a relation that
  does not mention layers at all.

## Results

Six side conditions:

| | Condition | Used by | Fails in | Failure |
|---|---|---|---|---|
| S1 | `static_code`: hosted (so analysed) code is static | conversion | `cx_static`: DeLaM with C computing | `csize ⌜(λx. x) 0⌝ ≡ csize ⌜0⌝`, so `4 ≡ 1` at M |
| W1 | `static_down`: nothing computing lifts into a static layer | conversion | `cx_sdown`: DeLaM with D ≤ C | the same, through the lift |
| S2 | `eval_up`: `run` at `j` of `c`-code needs `depth(typeof c) < depth(typeof j)` | normalization | `cx_eval`: the grid with every row running its own code | the liar |
| W2 | `depth_mono`: lifting never lowers the depth | normalization | `cx_depth`: code of M lifts into code of D (C₁ ≤ C₀) | the liar |
| W3 | `total_down`: nothing partial lifts into a total layer | normalization | `cx_total`: DeLaM with D partial | `fix x. x` at M |
| W4 | `eval_lift`: a layer runs only code that lifts into it | normalization | `cx_lift`: M runs partial C-code that does not lift into M | `run ⌜fix x. x⌝` at M |

Each counterexample structure meets the other five conditions
(`cx_*_others`), fails its own (`cx_*_fails`), and has a closed,
well-typed numeral at a total layer without a normal form, or a
conversion between two distinct numerals.

Under the conditions:
- `normalization` (S2, W2, W3, W4): a closed numeral at a total layer
  evaluates to a literal;
- `conv_sound` (all six): a conversion between closed numerals at a total
  layer relates two terms with the same literal.

The proof is a fundamental theorem by induction on the meta depth, then
on the derivation (`FT_depth`). The relation itself is not stratified:
code is related when both sides evaluate to one and the same well-typed
`box` (syntactic equality, because `csize` sees syntax). The depth is
used only at `run`: its code's contents were typed at a lower depth, so
the theorem at that depth applies to them. Nothing else looks inside a
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

- `grid_good`: the grid meets all six conditions for every depth `n`,
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

## For the refactor (#49)

The layer signature can be `LS`'s fields with S1, W1, S2, W2 and, once
partiality is wanted, W3 and W4. DeLaM meets them. Before trusting the
list in the dependent setting, three things differ from the toy:
- a recursor whose motive is a type family can decode code into a type,
  and decoding is a form of evaluation. So hosting at one's own depth
  (conjecture 2's relaxation) may need S2 to cover `elim_Typ` into a
  universe, not only `letbox`;
- the relation in the theories is layered (`LogRel/Layering.v`), so
  conjecture 3 may come back as a real condition there;
- code there is contextual, with global substitution; the toy's code is
  closed.
