# Syntax spike: generated or hand-written?

Question: can Autosubst (or any off-the-shelf generator) express DeLaM's syntax,
and if we write it by hand, does a representation exist whose substitution
laws are clean enough to automate?

## Answer

**Hand-write it.** The parts Autosubst cannot express are the core of
DeLaM, not edge cases. A hand-written representation
(`spike/Syntax.v`, 796 lines, 89 lemmas, ~2 s, **no axioms**) gets
**unconditional** composition and commutation laws. Only the identity laws
need a decidable syntactic invariant.

## What Autosubst cannot express

Checked against the paper (ch. 4 grammar, ch. 5 substitution operations):

| DeLaM feature | Why it falls outside Autosubst's model |
|---|---|
| `u^δ`: a global variable carrying a **stored** local substitution | Autosubst substitutions are meta-level functions. A syntactic δ must be composed *as syntax* (`u^δ'[δ] = u^{δ'∘δ}`). |
| Contextual instantiation `u^δ[σ] = σ(u)[δ[σ]]` | The substitute lives in a *different* local context and must then be closed by δ. Autosubst's instantiation returns `σ(u)` unchanged. |
| Context variables: `g` spliced into contexts, `wkᵏ_g[σ] = wkᵏ_{σ(g)}` | Expands one variable into several. Not a variable-for-term substitution. |
| Separate code scopes (`□(Γ ⊢ T)`, `box t`, context arguments) | Autosubst pushes every substitution into every subterm. There is no "this child has its own local scope". |
| Levels, layers, plain binders | Fine. Standard structure. |

## The representation (checked)

- **Local variables: de Bruijn.** A local substitution is a finite cons-list
  ending in a shift `lshift k`. A context variable is treated as an
  unknown-length block of indices, so the paper's two tails `·ᵏ` and `wkᵏ_g`
  are both "shift by k". *Which* tail it is is typing information, not syntax.
  Consequence: `wkᵏ_g[σ]` and its paper expansion `wkᵏ_{σ(g)}` are
  lookup-equal (`wk_expand`), so global substitution never has to expand
  anything.
- **Canonical outputs.** Every operation builds local substitutions with a
  smart constructor that absorbs redundant trailing variables. Normal local
  substitutions are equal iff their lookups are (`l_canon`). So substitution
  *arguments* are only ever used through lookups. This gives Autosubst-style
  extensional reasoning without funext.
- **Global variables: de Bruijn, one index space** (like the paper's single
  Ψ). A global substitution is a meta-level function to
  `gobj ::= GId j | GCtx Γ | GTm t`. `GId` makes identity and renaming
  sort-agnostic. Global substitutions never appear inside syntax, so they can
  stay functions.
- **The one cross-dimension cost.** A local substitution passing under a
  *global* binder must globally shift its entries (`gwk`). The paper uses
  named globals and never pays this. It is absorbed by the laws below.
  McTT's earlier locally-nameless global dimension is not needed.

## Proved laws

All are axiom-free (`Print Assumptions`: closed under the global context).

| Law | Condition |
|---|---|
| Local: renaming∘renaming, renaming∘subst, subst∘renaming, subst∘subst; `t[δ][ρ] = t[δ∘ρ]` | none |
| Global: renaming∘renaming, subst∘renaming, renaming∘subst, subst∘subst | none |
| Cross: `(t⟨r⟩)[σ] = (t[σ])⟨r⟩`, `(t[δ])[σ] = (t[σ])[δ[σ]]`, and the global-renaming versions | none |
| `renaming = subst` of the embedded renaming | none |
| Identity: `t[id] = t`, `t[σ_id] = t`, `t[id_Γ] = t` for the paper's `id_Γ` | `t` in normal form |
| Local β commutation `b[a/x][δ] = b[⇑δ][a[δ]/x]` | δ normal |
| Global β (letbox) commutation `b[o/u][σ] = b[⇑σ][o[σ]/u]` | σ's objects normal |
| Paper conformance: `u^δ[σ] = σ(u)[δ[σ]]`, `wkᵏ_g[σ] ≡ wkᵏ_{σ(g)}` | none |
| `letbox_ctx_weaken`: the context shift/renaming commutation McTT's letbox attempt lacked | none |

"Normal form" (`nft`) is decidable and syntactic: no absorbable local
substitution anywhere. Every operation's output is normal. Typed terms can be
made normal by a premise on the `u^δ` typing rule. This is the price of
storing substitutions in syntax: an Autosubst-style unconditional identity
law would need non-canonical syntax, and then *composition* breaks instead.

## Proof engineering

Ten of the law proofs are the same one-liner, `syn_start; law_auto`: mutual
induction, congruence, and canonicity for the `u^δ` case. The per-law work is
a few binder-commutation hint lemmas. Adding constructors should cost
automation time, not proof text. That needs confirming at full DeLaM size:
the Tarski split doubles the sorts, and there are ~40 constructors.

## Not covered

- Universe levels and level substitution: a third, plain variable sort.
- The Tarski type/term split: `U^δ` mirrors `u^δ`.
- The code-recursion branches: iterated binders of mixed sorts.
- Typing rules. The typing-level global weakening lemma is only exercised
  through `letbox_ctx_weaken`, the equation it needs.

## Reproduce

```sh
nix develop path:. --command bash -c 'cd spike && coqc Syntax.v'
```
