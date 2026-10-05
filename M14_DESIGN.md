# M14: length-indexed tuples and finite indices (`Vec`, `Fin`), design

Status: **M14a done, 2026-10-05** (outcome below); M14b, the codes, is
next. Why now: `HEATHER.md` item 5
lists `Vec` and `Fin` after `W`, and they are the substrate of Heather's
finitary `Wf` former (`H/docs/wf-former-design.md`). They are the first
type formers whose weak-head normal form is chosen by a term: a `Nat`
length, which is a bare term with no level of its own. Heather's own
`Vec` broke type-level preservation that way (`Vec^l(T;0) ⇝ Unit` dropped
the level, `H/issues/unit-level-and-vec-preservation.md`, closed by
level-indexing `Unit`), so our `preservation_ty` is the check that the
repair holds.

Heather's rules: `H/crates/kernel/DESIGN.md` (§Fragment, "index-computing
wrappers"), `H/crates/kernel/src/{typing,reduce}.rs`, paper pass
`H/docs/metatheory-ch07-extensions.md` §10.
- `Vec^l(T; k) @ l`, for `T @ l` and `k : Nat @ 0`. No binder: the length
  is a term in `Γ`.
- `Fin(k) @ 0`, for `k : Nat @ 0`.
- Four type reductions, at a canonical length:
  - `Vec^l(T; 0) ⇝ Unit^l`;
  - `Vec^l(T; S k) ⇝ Σ^{l,l}(_ : T). Vec^l(T↑; k↑)`;
  - `Fin(0) ⇝ Empty^0`;
  - `Fin(S k) ⇝ Unit^0 +^{0,0} Fin(k)`.
- Both reduce their length, and both are **neutral types at a neutral
  length**.
- No introduction or elimination forms of their own, and no η of their
  own: tuples are `Σ`-pairs ending in `⟨⟩`, indices are injections. What
  looks like `Vec`'s η (componentwise comparison, irrelevance at length
  0) is `Σ`'s and `Unit`'s, reached through the reduction.
- Codes `Vec^l(s; k) : Ty l` (decoding `El (Vec^l(s;k)) ⇝ Vec^l(El s; k)`,
  the length rides across) and `Fin(k) : Ty 0`, with four recursor
  branches (`t_Vec`, `t'_Vec`, `t_Fin`, `t'_Fin`).

Every choice above is Heather's. Gating follows M12 and M13: the formers at
layers D and M first, then every layer but V with the codes.

## Staging

- **M14a**: `Vec` and `Fin` at layers D and M, gated by `compt i`, with no
  code. Formation, congruence, the four computation rules, and every
  consequence.
- **M14b**: the codes, the lift to C and the four recursor branches.

## Syntax

- `tyVec l A n`: `Vec^l(A; n)`, no binder.
- `tyFin n`: `Fin(n)`, no binder and no level (it lives at `0`).

Both are appended to `ty` after `tyW`. Neither has a term former, so the
term-side case analyses (`whne`, `whnf`, the algorithmic term families)
gain nothing.

## Reduction (design point)

The first type reductions keyed on a term that is not a code. `El`'s
reductions read a code, and a code carries its own level; a length does
not. The untyped rules extend `red_ty`:

- `red_vec_zero l A : tyVec l A zero ⇝ tyUnit l`;
- `red_vec_succ l A n : tyVec l A (succ n) ⇝ tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩)`;
- `red_vec l A n n' : n ⇝ n' → tyVec l A n ⇝ tyVec l A n'`;
- `red_fin_zero : tyFin zero ⇝ tyEmpty lzero`;
- `red_fin_succ n : tyFin (succ n) ⇝ tySum lzero lzero (tyUnit lzero) (tyFin n)`;
- `red_fin n n' : n ⇝ n' → tyFin n ⇝ tyFin n'`.

`whne_ty` gains `whne_tyVec` and `whne_tyFin` at a `whne` length, exactly
as `whne_tyEl` sits on a `whne` code. Reduction stays deterministic: the
length position is the only one that reduces, and `zero`/`succ` are
`whnf`.

## Rules (M14a, gated by `compt i`)

- `wft_vec : lwf l → A @ l → n : Nat @ 0 → Vec^l(A; n) @ l`;
- `wft_fin : n : Nat @ 0 → Fin(n) @ 0`;
- `eqty_vec : l ≡ l' → A @ l → A ≅ A' @ l → n ≅ n' : Nat → Vec^l(A; n) ≅ Vec^{l'}(A'; n') @ l`;
- `eqty_fin : n ≅ n' : Nat → Fin(n) ≅ Fin(n') @ 0`;
- `eqty_vec_zero : lwf l → A @ l → Vec^l(A; 0) ≅ Unit^l @ l`;
- `eqty_vec_succ : lwf l → A @ l → n : Nat → Vec^l(A; S n) ≅ Σ^{l,l}(A). Vec^l(A↑; n↑) @ l`;
- `eqty_fin_zero : Fin(0) ≅ Empty^0 @ 0`;
- `eqty_fin_succ : n : Nat → Fin(S n) ≅ Unit^0 + Fin(n) @ 0`.

The `Σ` reduct lives at `l ⊔ l`, which is level-equivalent to `l`; the
rule states it at `l`, and its presupposition goes through `wft_lconv`.

## The relation: no new case (design point)

MX §10.1 predicts that neither former needs a clause of its own, and our
relation agrees: every type case begins `T ⤳* W @ l` and is closed under
typed weak-head expansion (`LR_red_ty`). So:

- at a length that reduces to `0` or `S k`, `Vec`/`Fin` are related by the
  `Unit`, `Σ`, `Empty` or `+` case of their reduct;
- at a neutral length, by `LRne`, with `Vec^l(A; ν)` a neutral type.

What *is* new is how the fundamental theorem builds the relation:
by induction on the length's `NatRel` (mutually with `NatNf`), not on the
type's syntax. `Vec^l(A; S k)`'s `Σ` has the codomain `Vec^l(A; k)` in
every weakening, which is the induction hypothesis carried through the
relation's weakening lemma. `Fin(S k)`'s `+` has the summands
`Unit^0` and `Fin(k)` at `Γ` (no Kripke quantification), which is the
induction hypothesis itself. The term relations' PER facts, which `LRsum`
carries, come from the relation's symmetry and transitivity.

The generic equivalence gains two neutral-type laws, MX §10.2's
"Congruence for Neutrals" at the type level:

- `gne_ty_vec : l ≡ l' → A ≈ A' @ l → ν ~ ν' : Nat @ 0 → Vec^l(A; ν) ~ Vec^{l'}(A'; ν') @ l`;
- `gne_ty_fin : ν ~ ν' : Nat @ 0 → Fin(ν) ~ Fin(ν') @ 0`.

As MX §10.2 says, `gne_ty_vec` is the first neutral-type law with a
*type* premise alongside the term one (`El ν`'s compares terms only). The
algorithmic families follow: `ac_tyne` gains `actne_vec` (levels, element
types by `ac_ty`, lengths by `ac_tmnee`) and `actne_fin`.

## Consequences to extend

Preservation (`RS_vec_zero`, `RS_vec_succ`, `RS_vec`, `RS_fin_*`):
type-level preservation at `Vec^l(A; 0) ⇝ Unit^l` at the same level `l`
is exactly what Heather's level-indexing round repaired. Type uniqueness,
type checking (`dec_tyVec`, `dec_tyFin`) and `neutral_univ` extend;
canonicity is unchanged (no term formers), and at a stuck length every
whnf is neutral (MX §10.1's lemma), which `LRne` already says.

## M14a outcome (2026-10-05)

Done at layers D and M, in one commit after the design. Every headline
theorem stays closed under the global context (`Print Assumptions` of
`wf_tm_dec`, `wf_ty_dec`, `consistency`, `closed_canonicity`,
`paper_sound`, `rec_red_typed`, `subject_reduction_tm`,
`subject_reduction_ty` and `V_vec_succ` lists nothing).

- **Syntax and reduction** as designed. `red_vec_succ`'s reduct shifts
  `A` and the length under `Σ`'s binder, so the renaming, level,
  universe-substitution and global-renaming stability lemmas of `red_ty`
  each gained a commutation step (`red_vec_succ_ren`, and one
  alternative in `red_leq_both`, `red_usubst_both`, `red_gren_both`).
- **Rules** as designed, gated by `compt i`. Presupposition gains
  `pre_vec_r`, `pre_vec_zero`, `pre_vec_succ`, `pre_fin_zero` and
  `pre_fin_succ` (the `Σ` reduct is formed at `l ⊔ l` and converted to
  `l` by `lmax_idem`). Inversion gains `inv_ty_vec` and `inv_ty_fin`,
  and static code, the layering predicate and the size measure their
  cases.
- **The relation gains no case**, as designed. `Validity/Vec.v` builds
  the relation at `Vec^l(A; m)` by induction on `NatRel m m'`
  (`LR_vec_nat`): expansion along the length's reduction, `Unit` at
  `0`, a neutral type at a neutral length (`gne_ty_vec`), and at `S k`
  `LR_vec_sig`, a `Σ` whose domain is `A` and whose codomain, in every
  Kripke world, is the induction hypothesis carried by `LR_kwk`
  (`vec_cod_single`: the codomain does not depend on the first
  component). `Fin` is the same with `Empty` and `+`; `+`'s summands are
  at `Γ`, so `LR_fin_sum` reuses `LR_sum_here`. Both `LR_vec_sig` and
  `LR_fin_sum` take the typed reductions to the reduct as premises, so
  the computation rules' validity (`V_vec_succ`, `V_fin_succ`) is the
  same lemma with the reduct itself on the right.
- **Validity**: `V_vec`, `V_fin`, `V_vec_zero`, `V_vec_succ`,
  `V_fin_zero` and `V_fin_succ`, with their global-substitution forms in
  `RulesS` (`VS_*`); `FundamentalS` and `FundamentalM` needed only the
  dispatcher entries.
- **Algorithm**: `actne_vec` (levels, element types by `ac_ty`, lengths by
  `ac_tmnee`) and `actne_fin`, through soundness, conversion, symmetry,
  transitivity (`ainv_vec`, `ainv_fin`), decidability and the `AlgEq`
  laws for `gne_ty_vec` and `gne_ty_fin`.
- **Consequences**:
  - Preservation: `RS_vec_zero`, `RS_vec_succ`, `RS_vec`, `RS_fin_zero`,
    `RS_fin_succ` and `RS_fin`. `Vec^l(A; 0) ⇝ Unit^l` preserves the type
    at the same level `l`, the check Heather's level-indexing round made
    possible.
  - Closed type canonicity: a closed `Vec` or `Fin` at a neutral length
    is impossible, as for `El` (no closed neutrals).
  - The head table (`ty_head`) gives `Vec` and `Fin` the neutral head:
    their only whnfs of their own are neutral.
  - Type uniqueness (`ty_lvl_uniq`) and type checking (`dec_tyVec`,
    `dec_tyFin`, deciding `compt i` first) extend; consistency and
    canonicity at terms are unchanged (no term formers).
- **Gotchas**: `LR_unit_red`'s right-hand level does not occur in its
  conclusion, so callers pass it (`(l' := l')`); `lequiv_refl _ _ I`
  cannot infer the level context, so `Fin`'s lemmas name `gL G`.

**Cost.** 34 files, about 750 lines added; `Validity/Vec.v` is 295 of
them. A clean `make -j2` took 654 s on the 2026-10-05 cloud machine
(608 s after the build-time pass, on a different machine, so the two do
not compare directly).
