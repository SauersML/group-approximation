---
rg: 2
id: sofic-action-class-commensurability-proof
kind: route
title: Restrict sofic embeddings to sub-crossed products, co-induce for subgroups, and use monomial induction for finite-index overgroups
target: sofic-action-class-closed-under-commensurability
requires: []
---

# Proof

All actions are p.m.p. on standard probability spaces, crossed products are von
Neumann crossed products with the canonical trace `τ(a u_g) = τ(a) δ_(g,1)`, and
"sofic" is Păunescu Definition 1.4.

## Lemma A (factors of restrictions)

Let `G ↷ (X,μ)`, `K <= G`, and let `A <= L^∞(X)` be a `K`-invariant von Neumann
subalgebra, `A = L^∞(Z)`. The von Neumann algebra generated inside
`L^∞(X) ⋊ G` by `A` and `{u_k : k ∈ K}` is trace-preservingly isomorphic to
`A ⋊ K`. Indeed the algebraic crossed product `A ⋊_alg K` sits inside both, the
two traces agree on it (both are `τ(a u_k) = τ(a) δ_(k,1)`), and a von Neumann
algebra with a faithful normal trace is the GNS completion of any weakly dense
∗-subalgebra for that trace.

So if `Θ` is a sofic embedding of `L^∞(X) ⋊ G`, its restriction is a sofic
embedding of `A ⋊ K`: `A` still lands in the diagonal and each `u_k` is still a
permutation. **A `K`-factor of the restriction to `K` of a sofic `G`-action is
sofic.**

## Lemma B (co-induction contains the seed)

Let `H <= G` be countable groups and `H ↷ (Z,ζ)`. Put
`CoInd_H^G(Z) = { f : G → Z : f(gh) = h^(-1)·f(g) for all g ∈ G, h ∈ H }` with
`(g·f)(g') = f(g^(-1) g')`. Choosing a transversal `T ∋ 1` of `G/H` identifies it
with `Z^T`, and the product measure `ζ^T` is `G`-invariant. For `h ∈ H`,

```text
(h·f)(1) = f(h^(-1)) = f(1·h^(-1)) = h·f(1),
```

so `f ↦ f(1)` is an `H`-equivariant measure-preserving factor map onto `Z` (its
marginal is `ζ`). **Every `H`-action is an `H`-factor of the restriction to `H`
of a `G`-action.**

## Part 1 (subgroups)

Let `G ∈ 𝒮`, `H <= G`, `H ↷ Z` arbitrary. `CoInd_H^G(Z)` is a `G`-action, hence
sofic. By Lemma B, `Z` is an `H`-factor of its restriction to `H`, so by Lemma A
`Z` is sofic. Thus `H ∈ 𝒮`.

## Part 2 (finite-index overgroups)

Let `[G:H] = n < ∞`, `H ∈ 𝒮`, `G ↷ (X,μ)` arbitrary. Fix a transversal
`t_1 = 1, ..., t_n` and write `g t_i = t_(π_g(i)) h(g,i)` with `π_g ∈ Sym(n)` and
`h(g,i) ∈ H`. Then `π_(gg') = π_g π_(g')` and
`h(gg',i) = h(g, π_(g')(i)) h(g',i)`. On the algebraic crossed product define

```text
ψ(f)   = Σ_i E_ii ⊗ (t_i^(-1)·f),
ψ(u_g) = Σ_i E_(π_g(i), i) ⊗ u_(h(g,i))      in  M_n(L^∞(X) ⋊ H).
```

* `ψ(u_g)ψ(u_(g')) = ψ(u_(gg'))` by the two cocycle identities, and
  `ψ(u_g)^* = ψ(u_(g^(-1)))` because `g^(-1) t_(π_g(i)) = t_i h(g,i)^(-1)`.
* Covariance: `ψ(u_g)ψ(f)ψ(u_g)^* = Σ_i E_(π_g i, π_g i) ⊗ (h(g,i) t_i^(-1)·f)`,
  and `t_(π_g(i))^(-1) g = h(g,i) t_i^(-1)`, which is the `(π_g i)`-th diagonal
  entry of `ψ(g·f)`.
* Trace: `(tr_n ⊗ τ)(ψ(f u_g)) = (1/n) Σ_(i: π_g(i)=i) τ(t_i^(-1)·f) δ_(h(g,i),1)`.
  Both conditions together say `g t_i = t_i`, i.e. `g = 1`, so this is
  `τ(f) δ_(g,1)`, the canonical trace.

So `ψ` extends to a normal trace-preserving embedding
`L^∞(X) ⋊ G → M_n(L^∞(X) ⋊ H)`. The restricted action `H ↷ X` is sofic because
`H ∈ 𝒮`; let `Θ` be a sofic embedding of `L^∞(X) ⋊ H` into `Π_(k→ω) M_(n_k)`.
Then `id_(M_n) ⊗ Θ` maps into `Π_(k→ω) M_(n n_k)`. It sends `E_ii ⊗ (diagonal)`
to diagonals, and `Σ_i E_(π(i),i) ⊗ (permutation)` to a block permutation matrix
whose blocks are permutations, which is a permutation. So
`(id ⊗ Θ) ∘ ψ` is a sofic embedding of `L^∞(X) ⋊ G`, and `G ∈ 𝒮`.

## Part 3 (consequences)

Commensurable groups share a finite-index subgroup `K`: if `G_1 ∈ 𝒮` then
`K ∈ 𝒮` by Part 1 and `G_2 ∈ 𝒮` by Part 2. If `H` has a nonsofic action `Z` and
`H <= G`, then `CoInd_H^G(Z)` is nonsofic: were it sofic, Lemmas A and B would
make `Z` sofic. `H` is not amenable (Păunescu Proposition 3.4), so `G` is
infinite, and multiplying by the Bernoulli shift of `G` gives an essentially free
action with `CoInd_H^G(Z)` as a factor, which is nonsofic by Lemma A with `K = G`.
