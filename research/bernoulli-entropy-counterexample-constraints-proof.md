---
rg: 2
id: bernoulli-entropy-counterexample-constraints-proof
kind: route
title: Compare Seward's Rokhlin values, co-induce to supergroups, restrict to finite index, and multiply by a base
target: bernoulli-entropy-counterexample-constraints
requires:
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
---

Rokhlin entropy is an isomorphism invariant, because an isomorphism carries
generating partitions to generating partitions of the same Shannon entropy.
Throughout, `phi: L^G → K^G` is the isomorphism, `s = h_sup(G)`, and "item n"
refers to `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`. The coordinate
partition of a Bernoulli shift is generating, so `h^Rok_G(L^G) ≤ h_1`.

**(a)** If `G` is sofic, item 4 gives Rokhlin entropies `h_1 ≠ h_2`.

**(b)** If `h_1 = 0`, then `lambda` is a point mass and `L^G` is a one-point
system, while `K^G` is not. So `h_1 > 0`, and `h_1 < h_2 ≤ ∞` gives `h_1 < ∞`.
Suppose `s > h_1`. By item 1, `h^Rok_G(L^G) = h_1`.
- If `h_2 < ∞`, item 1 gives `h^Rok_G(K^G) = min(h_2, s) > h_1`.
- If `h_2 = ∞`, item 2 gives `h^Rok_G(K^G) ∈ {0, ∞}`, and `h_1 ∈ (0,∞)` is
  neither.

Invariance fails either way, so `s ≤ h_1`.

**(c)** If `h_2 = ∞` and some free ergodic action has positive Rokhlin entropy,
item 2 gives `h^Rok_G(K^G) = ∞`, but `h^Rok_G(L^G) ≤ h_1 < ∞`.

**(d), supergroups.** Let `G ≤ G'`. For a p.m.p. `G`-space `Y`, put
`Coind(Y) = { f: G' → Y : f(tg) = g^(-1)·f(t) for t ∈ G', g ∈ G }`, with
`(g'·f)(t) = f(g'^(-1) t)`. It carries the product measure through
`f ↦ (f(r_i))_i` for a left transversal `(r_i)`.
- Define `Psi(x)(t) = (h ↦ x(th))`. Then `Psi(x)(tg)(h) = x(tgh) = (g^(-1)·Psi(x)(t))(h)`,
  and `Psi(g'·x)(t) = Psi(x)(g'^(-1) t)`.
- The inverse is `x(t) = Psi(x)(t)(1)`. On transversal coordinates `Psi` is the
  block decomposition of `L^(G')` along left cosets.
- So `Psi: L^(G') → Coind(L^G)` is a `G'`-isomorphism.
- `Coind(phi)(f)(t) = phi(f(t))` respects the defining condition by
  `G`-equivariance of `phi`, and is a `G'`-isomorphism.

Hence `L^(G') ≅ Coind(L^G) ≅ Coind(K^G) ≅ K^(G')`.

**(d), finite index.** Let `H ≤ G` with right cosets `G = ⊔_(j ≤ k) H s_j`. For
`h ∈ H`, `(h·x)(h' s_j) = x(h^(-1) h' s_j)`. So each block `L^(H s_j)` is
`H`-invariant and `H`-isomorphic to `L^H` through `y ↦ (h' ↦ y(h' s_j))`. The
restriction of `L^G` to `H` is therefore the `H`-Bernoulli shift with base
`(L^k, lambda^k)`, of entropy `k·h_1`; likewise for `K`. The map `phi` is
`H`-equivariant.

**(e)** For any base `(M,mu)`, `phi × id` is a `G`-isomorphism
`(L×M)^G = L^G × M^G → K^G × M^G = (K×M)^G`, with base entropies `h_1 + H(M)`
and `h_2 + H(M)`. Every `t ∈ [0,∞)` is the entropy of some finite base. By
`bernoulli-shifts-with-equal-base-entropy-are-isomorphic`, a Bernoulli class
depends only on base entropy, so the classes of `h_1 + t` and `h_2 + t` agree.
Translating `h_1 ~ h_1 + d`, where `d = h_2 − h_1`, by `t = d, 2d, ...` and
chaining gives the progression.
