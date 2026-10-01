# M13: well-founded trees (`W`), design

Status: **in progress** (M13a started 2026-10-01). Why now: `HEATHER.md`
item 5 lists `W` after `Empty` and `+`, and Heather's paper pass calls it
"the heaviest case" (MX §5). It is the first former whose term relation is
an inductive definition with a Kripke-quantified recursive premise, and the
only β rule whose right-hand side builds a binder found on neither side.

Heather's rules: `H/docs/delam-extensions.md` §9.
- `W^{l,l'}(x : S). T @ l ⊔ l'`, with `T` under the shape's binder.
- `sup^{l,l'}(x : S. T; a; f)`, with the child function
  `f : Π^{l', l ⊔ l'}(y : T[a/x]). W↑`.
- `elim_W^{l,l',l''}(x : S. T; z. M; a f ih. s; t) : M[t/z] @ l''`, a
  dependent motive and a step over the three-entry telescope
  `Γ, a : S, f : fty, ih : ihty`.
- β synthesizes the induction hypothesis
  `IH := λ^{l',l''}(y : T[a/x]). elim_W(…↑; f↑ y)`, and the step is
  instantiated at `a`, `f`, `IH`.
- No η: `W` is positive.
- A code `W^{l,l'}(x : s). t : Ty (l ⊔ l')` and four recursor branches
  `t_W`, `t'_W`, `t_sup`, `t_elimW`.

Every choice above is Heather's. Gating follows M12: the formers at layers
D and M first, then every layer but V with the code (M13b).

## Staging

- **M13a**: `W`, `sup`, `elim_W` and β at layers D and M, gated by
  `compt i`, with no code.
- **M13b**: the code, the lift to C and the four recursor branches.

## Syntax (de Bruijn)

Write `L := l ⊔ l'` and `W := tyW l l' S T`, with `S` in `Γ` and `T` in
`Γ, x : S`.
- `tyW l l' S T`, `T` under one binder.
- `tmSup l l' S T a f`, `T` under one binder.
- `tmElimW l l' l'' S T M s t`, `M` under one binder (the scrutinee `z`),
  `s` under three (`a`, `f`, `ih`, innermost last).

The step telescope, in de Bruijn form:
- `Γ_a = Γ, S`. Here `T` itself is `T[a/x]`: `a` sits where `x` was.
- `fty := Π^{l', L}(y : T). W⟨↑⟩⟨↑⟩`, in `Γ_a`.
- `ihty := Π^{l', l''}(y : T⟨↑⟩). M[↑³, app(var 1; l', L; T⟨↑⟩⟨↑⟩;
  W⟨↑⟩⟨↑⟩⟨rlift ↑⟩⟨rlift ↑⟩; var 0)/z]`, in `Γ_a, fty`. The application's
  annotations are `fty` weakened past `f` and `y`, literally.
- The step's type is `M[↑³, sup(S⟨↑³⟩; T⟨rlift ↑³⟩; var 2; var 1)/z]`.

β, at a `sup` of any annotations (as `case` steps at any injection):
`elim_W(S; T; M; s; sup(_; _; a; f)) ⤳ s[a, f, IH]` with
`IH := λ^{l', l''}(T[a/x]). elim_W(S⟨↑⟩; T⟨rlift ↑⟩; M⟨rlift ↑⟩;
s⟨rlift³ ↑⟩; app(f⟨↑⟩; l', L; T[a/x]⟨↑⟩; W⟨↑⟩⟨rlift ↑⟩; var 0))`. The
application's annotations are the child function's type weakened past `y`.

## The relation (design point)

MX §5 sketches `NfEqW`: a `sup` pair is related when the shapes are
related and, in every weakening, the children at related positions are
related by the outer relation at `W`. The recursive occurrence is under the
Kripke quantifier, so the relation is an inductive *family* whose context,
shape and family data change in the recursive premise.

- `WRel G Γ l1 l2 S T domR codR t t'` (with `WNf` mutually), with `G`,
  `Γ`, `S`, `T`, `domR`, `codR` indices. A child premise at `ρ` is at
  `kw_G ρ`, `kw_Δ ρ`, `kty ρ S`, `ktyl ρ T`, and the data composed with
  `ρ` (`fun ρ' => domR (kw_comp ρ ρ')`, as Weakening builds Π's).
- No identity weakening is needed: shapes are related in every weakening
  (`∀ ρ, domR ρ (ktm ρ a) (ktm ρ a')`), as `SigRel` relates first
  projections. The child premise quantifies over every proof `ha` of the
  shapes' relation at `ρ`, so the definition needs no weakening lemma for
  `domR`.
- Child applications are related for every choice of equivalent
  annotations, as in `PiRel`.
- The weakened data are not definitionally the composed data
  (`kw_comp` is associative only propositionally), so the relation's
  weakening, irrelevance and symmetry go through one transport lemma: `WRel`
  respects generically equal `S`, `T` and pointwise equivalent `domR`,
  `codR` (`codR` for any two proofs of the shapes' relation).
- The type relation `LRw` has `Σ`'s shape (`PolyFacts` at `tyW`, `domR`
  and `codR` in every weakening).
- The children's functions reduce to related whnfs in every weakening:
  `∀ ρ, WhRel … (Π^{l', L}(y : (ktyl ρ T)[ktm ρ a]). W↑) (ktm ρ f)
  (ktm ρ f')`, where `WhRel` is the first clauses of `PiRel` (both sides
  reduce, at the left type, to whnfs related generically). Without it a
  child function is related only through its applications, which does not
  say it has a whnf, and `elim_W`'s step takes `f` as an argument of type
  `fty`: its validity needs `f` related at `fty`, which is `PiRel`.
  Found when writing `elim_W`'s validity; added 2026-10-01. Kripke (not at
  the identity world) so that weakening composes it and symmetry,
  transitivity and level invariance convert its type at each world with
  the codomain's escape, as they do the annotations.
- The relation's lemmas: `WRel_dir`/`WRel_releq` (Escape), `WRel_flip`
  (Symmetry), `WRel_trans` (Transitivity, with `WhRel_trans`), `WNf_kw`/
  `WRel_kw` (Weakening), `WRel_leq` (LevelInv) and `WRel_perm` (UPermLR,
  over worlds that correspond along the permutation, `kcorr`; the backward
  direction is the forward one along `πi`).
