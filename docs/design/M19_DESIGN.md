# M19: indexed families with infinitary children (`IWi`), design

Status: **design** (2026-11-14). Nothing in the theories yet.

`IWi` is `IWf` (M17b) whose children are functions: a constructor has a
finite tuple of recursive fields, and field `i` is a function from its own
domain `D[a, i]` into the family. It is the kernel former for Heather's
`k: (y: A) -> D(e)` fields in an indexed family, today lowered to `W` plus
two stored equations (Heather's `docs/iwf-infinitary-design.md` §3). The
choice of this form over a single position type (indexed `W`, `M`'s
inductive dual) is argued in "Why a tuple of functions" below; the
background (risks, gains, the pruning probe) is
`PRUNE_VEC_WF.md` and the write-up linked from it.

## Why a tuple of functions

- **No stored equations.** `IWf`'s constructor sits at its index, so the
  index equation goes, as for `IWf`. A single position type packs a
  constructor's fields into a sum `A₁ + … + Aₙ`; a `match` arm's
  constructor form rebuilds the children function from the fields, which
  is convertible with the scrutinee's only with η for sums (or for
  `Empty`, at no fields). The kernel has neither, so the children equation
  (and the stored copy `k̄` of the fields, and a second `J` in `match`)
  would stay. A tuple has a component per field and η per component (Σ's
  and `Unit`'s), so nothing is rebuilt.
- **One to one with the surface.** A constructor's recursive fields are
  the tuple's components, in order; a plain child is a function from
  `Unit`.
- **Runtime.** A value is a shape and a Σ-chain of closures; a field at a
  literal position is `fst`/`snd` steps and an application. The cost is a
  closure for a plain child of a constructor that has a function field.
  Families without function fields stay on `IWf`, so ordinary data pays
  nothing.
- **Metatheory.** It combines `IWf`'s spine (`DVecISp`, `dnth`) with
  `W`'s Kripke children premise (`WNf`) per component. More than indexed
  `W` alone, paid once.

Kept as defaults (no fork): index-last as `IWf` (the constructor's index
is computed from its shape, `Ot[a]`); `IWf`, `W` and `Wf` stay formers
(folding them into `IWi` is `PRUNE_VEC_WF.md`'s question again, left open).

## Syntax (M19a)

Appended after `M`'s constructors, with `IWf`'s binder conventions:

- `tyIWi l lp li X A N D Ot C m`: `X` the index type at `li`; `A` the
  shapes at `l`; under `x : A` the arity `N` and the output index `Ot`;
  under `x : A, i : Fin N` the domain `D` at `lp`; under
  `x : A, i : Fin N, y : D` the child index `C`; the index `m`.
- `tmSupii l lp li X A N D Ot C a cs`;
- `tmElimIWi l lp li l' X A N D Ot C M c m t`, `M` under `j : X,
  z : IWi(j)`, `c` under `a, cs, ih`;
- the code `tmIWi l lp li x s n d o c m` (M19c).

Levels: the type lives at `iwiL l lp li := lmax (lmax l li) lp`.

Definitions (as `iwfFam`, `iwfIH`):

- `iwiFam a` (in `Γ, k : Fin N[a]`): `Π^{lp, L}(y : D[a, k]). IWi(…)(C[a, k, y])`,
  the type of field `k`, with `L := iwiL l lp li`.
- children: `DVec^L(N[a]; k. iwiFam a)`.
- `iwiIH c a cs := λ(i : Fin N[a]). λ(y : D[a, i]).
  elim_IWi(…; C[a, i, y]; app(dnth^L(N[a]; iwiFam a; cs; i), y))`.

Reduction: `red_elimIWi_supii` (β, below) and the congruence on the
scrutinee; `whne_elimIWi` at a `whne` scrutinee. No type reduction: `IWi`
is a whnf.

## Rules (M19a; `i <> lV`, β at `compt i`)

```
wft_iwi : X @ li, A @ l, (x:A) ⊢ N : Nat, (x:A, i:Fin N) ⊢ D @ lp,
          (x:A) ⊢ Ot : X, (x:A, i:Fin N, y:D) ⊢ C : X, m : X
          ⊢ IWi^{l,lp,li}(X; A; N; D; Ot; C)(m) @ iwiL l lp li

wf_supii : (the signature), a : A, cs : DVec^L(N[a]; k. iwiFam a)
          ⊢ sup(a; cs) : IWi(…)(Ot[a])

wf_elimIWi : (the signature), (j:X, z:IWi(j)) ⊢ M @ l',
          (a, cs, ih : Π^{0}(i : Fin N[a]). Π^{lp}(y : D[a,i]).
                         M[C[a,i,y], app(dnth(cs; i), y)]) ⊢ c : M[Ot[a], sup(a; cs)],
          m : X, t : IWi(m)
          ⊢ elim(…; M; c; m; t) : M[m, t]

β (compt i):  elim(…; Ot[a]; sup(a; cs)) ≅ c[a, cs, iwiIH c a cs]
```

with the congruences `eqty_iwi`, `eqtm_supii`, `eqtm_elimIWi` as
`IWf`'s (typed eliminator congruence, `ELIM_CONGRUENCE.md`: the step's
telescope types as premises, as `wf_elimIWf` states them). No η.

## The relation (M19b)

`LRiwi` is `LRiwf` plus a domain family: `idxR` (the index type, in every
world), `domR` (the shapes), and `posDomR`, the relation at `D[a, i]` for
related shapes and related positions (`PosRel`), in every world, as `W`'s
`codR` is over `domR`. The term relation is `IWf`'s three mutual
families with the index as an index:

- `IWiRel m t t'`: whnfs related generically and by `IWiNf m`;
- `IWiNf m`: two `sup`s whose annotations agree with the type's
  (`IWiEq`), shapes related in every world, `Ot[a]` related to `m` at `X`,
  children related by the spine in every world; or two neutrals;
- `DVecWSp c k cs cs'`: `DVecISp` with its head clause replaced by
  `WNf`'s children premise: the heads reduce, in every world, to whnfs
  related generically at `iwiFam`'s `Π` (as `PiRel`'s first clauses), and
  for related `y ~ y'` at `D[a, hd]` their applications (at any
  equivalent annotations) are related by `IWiRel` at `C[a, hd, y]`. The
  tail is the spine at the moved families (`posMv` on both `C` and `D`).

`elim_IWi`'s validity is `elim_IWf`'s induction over the three families;
the induction hypothesis at a field is a `λ` over `y` (as `elim_W`'s),
built from the spine's head premise. The child index `C[a, i, y]`
depends on `y`, so relating two children's indices needs `C`'s validity
at related `y ~ y'`, which the signature's premises give, as `M18b`'s
child index did.

## Staging

- **M19a**: syntax, substitution and renaming laws, reduction, the typing
  rules and the typing metatheory (weakening, substitution, inversion,
  presupposition) at every layer but V, β at D and M.
- **M19b**: the relation, validity, the fundamental theorem, the
  algorithm, decidability, the type checker, canonicity (a closed term
  at `IWi` computes to a `sup`).
- **M19c**: the code `tmIWi`, its decoding, the lift to layer C and four
  recursor branches (`ty_iwi`, `tm_iwi`, `tm_sup_ii`, `tm_elim_iwi`),
  ahead of Heather's `rec.rs`.

Template: M17b (`IWf`) for every file; `W` (M13) for the children
premise; M18b (`M`) for an infinitary child index.
