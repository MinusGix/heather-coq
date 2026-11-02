# Löb at the reflexive cell R (issues #47, #54)

Status: **probe done** (2026-11-02), `probes/Lob.v`, standalone, no
axioms (`Print Assumptions` closed for every result below). The theories
are untouched.

The question (#47): can a layer get intensional recursion, a program that
receives its own code, without the liar? `LAYER_STRUCTURE.md` found the
slot for it in the grid: the reflexive cell R, a program row that hosts
and analyses its own code but runs it only from one level up. This probe
puts Löb's rule there and checks the metatheory. It also answers part of
#54 (a first-class later modality), below.

## The toy

STLC with `Nat` and `Empty`, two layers R (depth 0) and U (depth 1) with
R ≤ U, and `▷A`: R's typed, closed code of type `A`, formable at both.

| Former | Rule | Where |
|---|---|---|
| `lbox s` | `⊢_R s : A` gives `⌜s⌝ : ▷A` | R, U |
| `lfix A M` (Löb) | `z : ▷A ⊢_R M : A` gives `lfix z. M : ▷A` | R, U |
| `llob A t` (GL axiom) | `▷(▷A → A) → ▷A`, `llob ⌜f⌝ ⇝ lfix z. f z` | R, U |
| `lapp B t u` (K) | `▷(A → B) → ▷A → ▷B` | R, U |
| `csize t` | the size of the code's syntax tree | R, U |
| `evalg t d` | grounded release: runs code headed by `lbox`, returns `d` for `lfix` | R, U |
| `runk n t d` | fuelled run: the delay observed for `n` steps | R, U |
| `run t` | release, axiom T: `run ⌜s⌝ ⇝ s`, `run (lfix z. M) ⇝ M[lfix z. M / z]` | U only |

`lfix` is an opaque code node: reduction never unfolds it except under a
run, and `csize` sees it as a node. K keeps code headed by `lfix`
ungrounded: `⌜s⌝ ⊛ ⌜u⌝ ⇝ ⌜s u⌝`, but if either side is an `lfix` the
result is an `lfix` whose variable is unused.

## Results

- **Normalization** at both layers (`normalization`), so `Empty` and
  `▷Empty` are empty (`Empty_empty`, `later_Empty_empty`). U's `run` is
  total over code with Löb in it: running an `lfix` unfolds it once, into
  an R-term that cannot run its own code without fuel.
- **Löb holds at R**: the rule (`lob_rule`), the GL axiom and K as closed
  R-terms (`lob_axiom`, `k_axiom`). Kleene's second recursion theorem is
  `lob_unfold`: `llob ⌜f⌝ ⇝ L` and `run L ⇝ f L`.
- **R cannot prove its own consistency** (`no_R_consistency`): no closed
  R-term has type `▷Empty → Empty`, while U has `λx. run x`
  (`U_consistency`). This is Gödel's second theorem as GL has it (`□⊥ → ⊥`
  is not a theorem). The proof is a second model of the same fundamental
  theorem, in which `▷A` at R also holds *holes* (unknown code with no
  contents): R's terms are parametric in the code they cannot run, and a
  function of type `▷Empty → Empty` would take the hole to an element of
  `Empty`.
- **The fuelled liar** (`fuel_liar`): `runk n (lfix z. succ (runk n z 0)) 0`
  is typed at R and reduces to `succ (succ (… 0))` with `n` `succ`s, so it
  answers `n`. With `run` at R, the same liar, `lfix z. succ (run z)` run,
  passes through `succⁿ liar` for every `n` (`liar_nat_trace`) and
  diverges (`liar_nat_diverges`): its trace is the never-ending delay, and
  fuel `n` is that trace cut after `n` unfoldings with the default in the
  hole. Each unit of fuel is one unfolding of `lfix`.
- **Grounded release** (`gliar_*`): with `evalg` in place of `run`, the
  liar `lfix z. succ (evalg z 0)` is refused at R (`evalg` of it answers
  its default), and U running it answers `1`: one unfolding, then the
  refusal.

The proof is a fundamental theorem by induction on depth, then on fuel,
then on the derivation (`FT_depth`), as in `LayerStructure.v`. The
relation at `▷A` is syntactic (both sides evaluate to one well-typed code
value, since `csize` sees syntax). Grounded code also carries the
relation of its contents, which is what makes `evalg` safe at R's own
depth. Nothing is asked of an `lfix`'s contents: asking would be the
circle that Löb closes, and it is why the relation needs no step index.
Running an `lfix` is justified instead by the theorem one depth down (`run`
at U) or at lower fuel (`runk`).

## The side conditions

Four, each with a counterexample that breaks normalization or
conversion soundness:

| | Condition | Counterexample | Failure |
|---|---|---|---|
| L1 | no T at R: R does not `run` its own code (`eval_up`, S2 of `LAYER_STRUCTURE.md`) | `cfg_tR` | `liar A = run (lfix z. run z)` inhabits every type at R, `Empty` included (`liar_typed`), and reduces to itself (`liar_diverges`) |
| L2 | Löb's body is closed: it sees only its own variable | `cfg_open` | `(λe. run (lfix z. e z)) (λx. run x)` is typed at U and diverges (`oliar_*`): an open body takes in a release from above |
| L3 | `lfix` is opaque: no conversion unfolds it | `unfold_csize`, `unfold_evalg` | `lfix z. 0` and its unfolding `⌜0⌝` differ by `csize` (2 against 1) and by `evalg` (refused against run), so no conversion that is a congruence for `csize` and sound for numerals has unfolding (`no_unfolding_conversion`) |
| L4 | code formers keep `lfix`-headed code ungrounded | the `leak` reduction of K | `X := evalg ((lfix z. λx. succ (evalg (z ⊛ ⌜0⌝) 0)) ⊛ ⌜0⌝) 0` is typed at R; with K grounding its result, `X ⇝* succ X` and diverges (`kX_leak_diverges`); in the sound reduction `X ⇝* 0` (`kX_sound`) |

L1 is the layer-structure probe's S2, unchanged. L2 is the restriction
of Kavvos's iPCF (the fixed point's body sees only modal hypotheses), and
DeLaM's `box` already has it: code's contents live in the global context,
never the local one. Precisely, the body must not capture a variable of a
layer that releases the code. The closed body is the simple sufficient
form. L3 is S1 (analysed code is static) applied to a code former's own
computation rule. L4 is new: Weaver's meaningfulness predicate is the
code's head, but every operation that builds code has to propagate it.

Groundedness needs only the head, not deep fix-freeness. Grounded code
may contain `lfix` codes as data; running it at R is safe, because R can
run those only with fuel or grounded release, so they never unfold
without bound.

## What this means for a first-class later modality (#54)

- **▷ already is guarded recursion, closed.** `next` is `lbox` (for
  closed terms), `⊛` is K (`lapp`), Löb is `llob`, and a guarded
  `fix : (▷A → A) → A` exists one layer up: `gfix f := run (llob ⌜f⌝)`, with
  `gfix f ⇝* f L` and `run L ⇝ f L`, so `L` is `next (gfix f)`
  (`gfix_unfold`).
- **The exit from ▷ is the next layer, not a clock.** Guarded type theory
  needs clocks so that `force` never reaches a fixed point's own
  variable. Here that job is done by L2 (the body is closed). An
  extensional ▶ with `next : A → ▶A` on open values and
  `fix : (▶A → A) → A` at a layer is `cfg_open`'s shape. Such a ▶ can have
  an exit only where no fixed point's body can see it: either no `force`
  at all (normalizing, but there is no way out of ▶, #54's question 1), or
  clocks. So #54's "the layers act as clock ticks" holds in this sense:
  T one layer up is total over code with Löb (`normalization` at U), and
  each run spends one tick.
- **`run : ▷A → Delay A` belongs to the same layer.** The #47 discussion
  proposed it for the layer above R. From one layer up, `run : ▷A → A` is
  total: one unfolding exposes an R-term, which cannot run its own code
  unboundedly. The delay appears where a layer runs code of its *own*
  depth: there it is the fuelled run (`runk`, the delay observed for `n`
  steps), and without fuel it is the liar's never-ending trace. A layer's
  own `Delay`-valued run therefore needs no new metatheory beyond fuel.
  Building `Delay` as `M` with shape `A + Unit` (M18) is still needed for
  one thing: to state it as a type with `never` in it, not only as its
  observations.
- **A forgetful map `□A → ▶A`** is `next` for closed code here. For open
  code it is the open ▶, which the above rules out unless clocks come
  with it.

## Simplifications

Each is a place where the result could change in the real system:

- code is closed, with no contextual types and no global context;
- there are two layers, not the grid. Every program row of the grid
  gets Löb on its own code in the same way, with T from the row above
  (argued, not checked). The proof would be `LayerStructure.v`'s
  stratification with this probe's relation at `▷`;
- there is no conversion judgment, only the observational argument of
  `no_unfolding_conversion`. `LayerStructure.v`'s conversion soundness
  should carry over with static code (argued, not checked);
- simple types: running a code of `▷A` gives an `A`, a smaller type,
  so U can run code only as often as its term says. With recursive types
  (#54's guarded recursive types, `A ≅ ▷A → B`), U could iterate `run`
  without bound, and its totality would need an analysis of its own;
- no dependent recursor over `▷`-code. `LAYER_STRUCTURE.md`'s caveat
  applies: a motive "the meaning of the code" turns a recursor into an
  evaluator, which here would be T at R.
