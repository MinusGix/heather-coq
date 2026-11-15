# Retiring `Vec` and `Wf` into `DVec` and `IWf`: a probe

Status: probe done (2026-11-14), `probes/PruneVecWf.v`. No theory changed.

Heather's `docs/iwf-former-design.md` §10 targets option 2: `Vec^l(T; k)`
spelled `DVec^l(k; _. T)` and `Wf^l(A; x. N)` spelled
`IWf^{l,0}(Unit; A; x. N; _. ⟨⟩; _ _. ⟨⟩)(⟨⟩)`. The question was whether
that adds strength and what it loses. `W`, `Fin`, `Σ`, `Unit`, `+`, `Empty`
and `Nat` stay: `DVec`, `dnth` and the arities compute to them, and `W` is
infinitary.

## Strength

None is added. The pruned system's rules are a subset of today's, so every
judgment it derives is derived today, and consistency, canonicity,
normalization and decidable conversion carry over with no new proof. The
probe checks the other direction: which of the 17 dropped rules the
translation still derives, and what it loses.

## What translates (checked at layer D)

At a generic instance (shape `El a` for a code variable `a`, arity `nf x`
for a function variable `nf`, so every `Wf` whose shape has a code at level
0 is a substitution instance), by `IwfCheck.v`'s checker:

| dropped rule | translated by | lemma |
|---|---|---|
| `wft_vec` | `wft_dvec`, the family weakened | `vec_as_dvec_ty` |
| `eqty_vec_zero`, `eqty_vec_succ` | `DVec`'s two reductions | `vec_as_dvec_zero`, `vec_as_dvec_succ` |
| `wft_wf` | `wft_iwf` at `Unit`, then `lmax l 0 ≈ l` | `wf_as_iwf_ty` |
| `wf_supf` | `wf_supi`; `C[a, k]` is `⟨⟩` after substitution | `supf_as_supi` |
| `wf_elimWf` | `wf_elimIWf`, motive weakened past `j` | `motive_retypes`, `elim_as_elimIWf` |
| `eqtm_elimWf_supf` | `eqtm_elimIWf_supi`, open `a` and `cs` | `elim_as_elimIWf_beta` |

The congruences (`eqty_vec`, `eqty_wf`, `eqtm_supf`, `eqtm_elimWf`) and the
code rules (`wf_code_vec`, `wf_code_wf`, `eqty_El_vec`, `eqty_El_wf`,
`eqtm_code_vec`, `eqtm_code_wf`) map one to one onto `DVec`'s and `IWf`'s,
with the same premises up to weakening. They are not checked here.

Levels are no obstacle: the translated type sits at `lmax l 0`, which
`wft_lconv` and the annotations' `lequiv` take to `l`.

## What is lost

1. **The eliminator at layer C.** `elim_IWf`'s motive ranges over
   `j : Unit, z : τWf(j)`; `elim_Wf`'s over `z : Wf`. At layers D and M the
   old motive retypes because `Unit`'s η makes `j ≡ ⟨⟩`
   (`generic_index_D`). At layer C equality is syntactic up to levels
   (`static_code_eqty`), so `τWf(j)` and `τWf(⟨⟩)` are different types
   (`generic_index_not_C`). A motive that uses `z` where the fixed instance
   is expected (`Id(Wf; z; w)` for a context `w : Wf`, or `f z` for
   `f : Wf → Nat`) has no `elim_IWf` spelling at C: generalizing `w`'s or
   `f`'s type to `τWf(j)` is not possible for a variable of the context,
   and rebuilding `z` at `⟨⟩` by an `elim_IWf` does not reduce back to `z`
   at C (argued; the probe checks the inequality of the two types). Code that eliminates unindexed data under such a motive would stop
   type-checking at the code layer. It is the same restriction indexed
   families have today, extended to all data.
2. **`nth`'s tail equation, through the induction hypothesis.**
   Today `nth(S k; cs; inr j) ≡ nth(k; snd cs; j)` at a neutral `k`
   (`nth_tail`): the unfolding at the successor is the same `natrec` at
   `k`. `elim_IWf`'s induction hypothesis reads the children through
   `dnth`, whose unfolding at `inr j` is a `natrec` at `k` whose motive
   embeds into `Fin (S k)`, applied to `λy. inr y`, while `dnth(k; snd cs;
   j)` embeds into `Fin k`. They are not convertible
   (`dnth_tail_not_conv`, by inverting the algorithm through
   `ac_complete_tm`: the two motives differ at `Fin (S k)` against `Fin k`).
   So an `elim_Wf` step that hands `λj. ih (inr j)` to a helper expecting
   the tail's induction hypothesis, at a neutral arity such as
   `S(fst a)`, stops type-checking under a dependent motive. At a literal
   arity both reduce to projections and agree. Heather's lowering cases on
   the tag before reading children, so its arities are literal there; only
   hand-written kernel terms with a computed arity meet this. Keeping
   `nth` itself as the constant-family accessor over `DVec` (its own
   `natrec`, no embedding) keeps the equation for vector code; the loss is
   confined to the induction hypothesis.
3. **Code analysis.** The code recursor's `Vec` and `Wf` branches (Heather:
   `ty_vec`, `tm_vec`, `ty_wf`, `tm_wf`, `tm_supf`, `tm_elim_wf`) merge
   into `DVec`'s and `IWf`'s. A meta-program recognizes a plain vector by
   checking that the family ignores its position, not by its head.

A neutral length no longer separates `Vec` from `DVec`: there is one
spelling.

## Reading for Heather

Option 2 is sound and adds nothing. It removes 6 of the recursor's 65
branches and the `Vec`/`Wf` cases of the kernel (about 275 kernel lines
mention them, a measure of reach rather than of what would be deleted).
Its costs are item 1 (the code layer) and item 2 (a hand-written
eliminator at a computed arity). Neither touches what the elaborator
generates at layers p and m today.
