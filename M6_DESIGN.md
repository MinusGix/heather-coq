# Milestone 6: algorithmic convertibility and its decidability

Goal: the paper's second instantiation of the generic equivalence. That is
the convertibility-checking judgments, their soundness and completeness
with respect to declarative equality, and the decidability of convertibility
of well-typed types and terms at the computing layers D and M. With M1–M5
this completes the paper's development. The user's extensions (more layers,
2D structure, local computation rules) come after it.

Paper references: 06:351–723 (the judgments, soundness), 08:73–372 (the
instance, the conversion lemma, PER, convertibility, decidability). The
proof follows Abel, Öhman and Vezzosi 2017, as does logrel-coq's
`AlgorithmicConvProperties`/`Decidability`.

## Scope

| Stage | Contents |
|---|---|
| **M6** (this doc) | decision procedure for `lequiv`/`≡ₗ`; the algorithmic judgments at D and M; soundness; the algorithmic instance of `GenericEqLaws` (D and M) and `GenericEqM`; completeness via the FT and escape; decidability |
| later | the user's extensions |

## Decisions

### H1. Decidability is stated in `Prop`

The theorem is `A \/ ~A` for the algorithmic (equivalently the
declarative) judgment, proved constructively with no axioms beyond the
design's. The proof goes by induction on reflexive algorithmic derivations
(08:236), which live in `Prop`, so a `sumbool` would need `Type`-valued
derivations throughout. An executable checker (logrel-coq's fuel-based one)
is a possible follow-up, not part of M6.

### H2. One family of judgments, with neither layer nor level

The paper's nine judgments are one mutual inductive, `ac_* G Γ …`, with
the paper's names:

| Coq | paper | meaning |
|---|---|---|
| `ac_ty` | `⊢ T ⇔ T'` | types (reduce to whnf, then compare) |
| `ac_tynf` | `⊢ W ⇔nf W'` | whnf types |
| `ac_tyne` | `⊢ V ⇔ne V'` | neutral types |
| `ac_ctx` | `⊢ Γ ⇔ Δ` | local contexts (pairwise) |
| `ac_tm` | `⊢ t ⇔ t' : T` | terms (reduce type and terms, compare) |
| `ac_tmnf` | `⊢ w ⇔nf w' : W` | whnf terms at a whnf type |
| `ac_tmne` | `⊢ ν ⇔ne ν' ▷ T` | neutral terms, type inferred |
| `ac_tmnee` | `⊢ ν ⇔ne ν' ▷ W` | neutral terms, inferred type reduced |
| `ac_sub` | `⊢ δ ⇔ δ' : Δ` | local substitutions (pointwise) |

The `ac_` prefix avoids the existing `conv_tm` (Escape.v).

The judgments carry no layer and no level. The instances bundle
declarative typing at their layer and level (H4), so:

- level annotations are compared with the semantic `leqv`, which agrees
  with `lequiv (gL G)` on well-formed levels (bundled typing gives
  well-formedness). No level-conversion rules are needed, so derivations
  are syntax-directed;
- a layer-M rule never fires on inputs typed at D: typing inversion at D
  rules the head out.

The algorithm keeps `G` and `Γ` for the inferred types of variables and
global variables. Binders extend them as the typing rules do (`Γ ,, A @ l`,
`gctx_uwk n G`/`Γ⟨ush n⟩ᵤ`, `gext G _`/`Γ⟪S⟫`).

Other departures from the paper's rules (06:381–700):

- the reductions are untyped, and their targets are required to be whnf;
- neutral terms reach `⇔nf` only at a *positive* whnf type (`Nat`, `U`,
  a neutral type, `CTyp`, `CTrm`). The paper forgets `U`. At function
  types (`Π`, `UΠ`, `CΠ`, `TΠ`) only the η rule applies;
- where the paper checks the inferred type of a neutral head against a
  fixed shape (`El`, `app`, `natrec`, `letbox`, the recursors), the rule
  ignores it (as the paper says for `app`). Soundness gets the right type
  from the bundled typing and neutral type uniqueness (H7). `uapp`,
  `capp` and `tapp` read their result type from the inferred `UΠ`/`CΠ`/`TΠ`;
- `succ` compares its argument with `⇔`, not `⇔nf` (06:447 is a typo);
- `ac_sub` is pointwise over `in_ctx Δ`. The tails of two typed
  substitutions between the same contexts agree (`lsub_tail`), so the
  entries suffice. The premise `forall n A k, in_ctx Δ n A k -> ac_tm …`
  is strictly positive, and Δ is finite, so decidability is unaffected.

### H3. Levels up to `leqv`, boxes up to `≡ₗ`

`leqv` is semantic (equal evaluation under every valuation), so M6 needs a
decision procedure. A level evaluates to `max(c, max_x (v x + k_x))` with
`c` its value at the zero valuation and `k_x` the offset of the variable
`x` (`leval_split`). Two levels are equivalent iff they have the same `c`
and the same offsets (`leqv_iff`: take `v` large at one variable and 0
elsewhere). Only finitely many variables occur, so this is decidable.
Boxed code is compared by `ty_leq`/`tm_leq` (E11: the Static Code Lemma
gives syntactic equality up to `≡ₗ`), which is structurally decidable given
`leqv`. Soundness of the box rules is `eqtm_leq` at M.

### H4. The instance is bundled

As in logrel-coq, the generic relations carry declarative well-formedness
beside the algorithmic derivation:

- `geq_ty` := `ac_ty` ∧ `⊢ Γ` ∧ both types well-formed;
- `geq_tm` := `ac_tm` ∧ both terms typed at `T`;
- `gne_ty` := `ac_tyne` ∧ both types well-formed;
- `gne_tm t t' T` := `∃ T'`, `ac_tmne t t' ▷ T'` ∧ `T ≅ T'` declaratively ∧
  both typed at `T`.

The last is the paper's "hide a syntactic equivalence judgment inside"
(08:195). It removes the left bias of inference, which makes symmetry,
transitivity and type conversion provable (08:199).

### H5. The recursor neutrals

The algorithm compares the motives, the thirteen branches, `l`, `Δ` (and
`T`) and the scrutinees (`ac_tmnee`, or `tm_leq` for boxed global variables).
It never uses a declarative premise. The interface's declarative motive
instance equation (E10) is a premise of the law, so the bundled instance
has it anyway.

### H6. Soundness through normalization

The algorithm uses untyped reduction, and soundness needs its equation.
For a well-typed input, normalization (`decl_whnf_normalization_*`,
`declM_whnf_normalization_*`) gives a typed reduction to some whnf, and
untyped reduction to whnf is deterministic (`reds_whnf_det`), so it is
the algorithm's whnf. Soundness is proved after the declarative
consequences, which the order of the proofs allows: soundness is only
needed by the algorithmic instance.

### H7. Typing inversion and neutral type uniqueness

The paper's neutral soundness uses that "ν and ν′ are well-typed so the
type annotations must be equivalent" (06:589). This needs typing
inversion for every head (`var`, `gvar`, `natrec`, `app`, `letbox`, the
recursors, `uapp`, `capp`, `tapp`). It also needs neutral type
uniqueness: a whne term's types are equal, at equivalent levels. The only
generic typing rules are `wf_conv` and `wf_lconv`, so inversion is by
induction on typing. Inversion is new metatheory (`Typing/Inversion.v`),
proved before soundness.

## Order of the proofs

1. **Levels** (`Syntax/LevelDec.v`): `leqv`, `lequiv`, `ty_leq`, `tm_leq`,
   `ctx_leq`, `lsub_leq` decidable.
2. **Judgments** (`Typing/Algorithmic.v`), **typing inversion and
   neutral type uniqueness** (`Typing/Inversion.v`), **soundness**
   (`Validity/AlgSound.v`): algorithmic ⇒ declarative, for well-typed
   inputs.
3. **Structural properties**: weakening (local, global, universe
   substitution), `≡ₗ` closure, whnf ⇒ general, reflexivity of neutrals.
4. **Conversion lemma and PER** (08:94–229), using the declarative
   consequences: injectivity of every type former, discrimination, whnf
   determinism (`tyred_whnf_det`, `tmred_whnf_det`).
5. **The instances** (`AlgInstance.v`): `GenericEqLaws` at D and M,
   `GenericEqM`; completeness by `fundamental`/`fundamentalM` with the
   algorithmic pair and escape.
6. **Decidability** (08:236–372), by induction on one reflexive derivation
   and inversion of the other. The final theorem decides declarative
   equality of two well-typed types or terms.

## Status

Design only.
