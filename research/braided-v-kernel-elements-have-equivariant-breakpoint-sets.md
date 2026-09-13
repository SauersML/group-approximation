---
rg: 2
id: braided-v-kernel-elements-have-equivariant-breakpoint-sets
kind: claim
title: "Nontrivial elements of the pure braided kernel of braided V carry finite nonempty dyadic breakpoint sets moved by conjugation through T"
---

Let `π: bV → V` send a triple `(T_-, β, T_+)` to `(T_-, σ_β, T_+)`, forgetting the braid to its
permutation, and let `K = ker π`. There is a map E from `K ∖ {1}` to the finite nonempty subsets
of `Z[1/2]/Z` such that `E(hkh^{-1}) = π(h)(E(k))` for every `h ∈ bV` with `π(h) ∈ T`.

**Construction.**
- Represent k as `(S, β, S)`, with β a pure braid on the leaves of S. Every kernel element has such
  a representative, and it is trivial iff β is.
- `r(k)` is the least size of a strand set Q whose restriction `f_Q(β)` is nontrivial; the
  restriction deletes the other strands.
- `B(k) ⊆ (R/Z)^r` is the union of the products `I_{q_1} × ⋯ × I_{q_r}` of closed dyadic leaf arcs,
  over all minimal Q and all orderings of Q.
- `E(k)` is the set of points x such that, along some coordinate circle, the indicator of `B(k)`
  is not locally constant at x.

**Why it works.**
- Cabling a strand is injective and commutes with deleting other strands, so `r(k)` and `B(k)` do
  not depend on the representative.
- Conjugating a pure braid by a braid permutes its minimal strand sets.
- `E(k)` is nonempty because `B(k)` is neither empty nor all of `(R/Z)^r`: it misses `(x, …, x)` for
  every non-dyadic x.

Route: `braided-v-kernel-elements-have-equivariant-breakpoint-sets-proof`.
