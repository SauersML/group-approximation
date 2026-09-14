---
rg: 2
id: group-ring-domains-local-embedding-proof
kind: route
title: Push a zero divisor forward along a multiplicative injection of its support and its products
target: group-ring-domains-pass-to-local-embeddings
requires: []
---

**Proof.** Let `alpha, beta in k[G]` be nonzero with `alpha beta = 0`. Put
`F = {1} ∪ supp alpha ∪ supp beta`, and let `psi: F·F -> H` be as in the claim.
Define

    alpha' = sum_(a in supp alpha) alpha_a psi(a),
    beta'  = sum_(b in supp beta)  beta_b  psi(b)     in k[H].

1. `psi` is injective on `F ⊆ F·F`, so the coefficient of `psi(a)` in
   `alpha'` is `alpha_a`. So `alpha' != 0` and `beta' != 0`.
2. In `k[H]`, `alpha' beta' = sum_(a,b) alpha_a beta_b psi(a) psi(b)`.
   Multiplicativity gives `psi(a) psi(b) = psi(ab)`. Injectivity on `F·F`
   gives `psi(ab) = psi(a'b')` exactly when `ab = a'b'`. So for every
   `g in F·F` the coefficient of `psi(g)` in `alpha' beta'` is
   `sum_(ab = g) alpha_a beta_b`, the coefficient of `g` in `alpha beta`,
   which is `0`. Every other element of `H` has coefficient `0`.
3. So `alpha' beta' = 0` with both factors nonzero, contradicting that `k[H]`
   is a domain.

**Corollary.** Let `(H_n, S_n) -> (G, S)`. Fix `R` with `F ⊆ B_G(R)`. By the
definition of the topology, for large `n` the words of length at most `4R` in
`S^(+-1)` that represent `1` in `G` are exactly those whose image represents
`1` in `H_n`. So the map `w(S) -> w(S_n)` on words of length at most `2R` is
well defined and injective on `B_G(2R) ⊇ F·F`: two such words agree in `G`
exactly when `u v^(-1)`, of length at most `4R`, is trivial, and likewise in
`H_n`. It is multiplicative on `F × F` because concatenating words of length at
most `R` gives a word of length at most `2R`. Apply the claim for the infinitely
many `n` where `k[H_n]` is a domain.
