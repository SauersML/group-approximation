---
rg: 2
id: wedges-of-spheres-have-free-cyclic-cover-homology
kind: claim
title: "Connected infinite cyclic covers of a wedge of spheres have free twisted homology, giving a computable non-wedge certificate"
distinct_from:
  some-finite-planar-set-has-a-non-wedge-rips-complex: that claim asks for a planar counterexample; this one is a general algebraic-topology test that such a counterexample would pass
---

Let `T` be a connected CW complex homotopy equivalent to a wedge of spheres
`∨_{i∈I} S^{n_i}` (all `n_i ≥ 1`), let `T̃ → T` be a connected infinite cyclic
covering with deck generator `t`, and let `k` be a field. Then:

1. `H_q(T̃; k)` is a free `k[t^{±1}]`-module for every `q ≥ 1`, and
   `H_0(T̃; k) ≅ k[t^{±1}]/(t − 1)`.
2. **Certificate.** Suppose `T` is a finite complex. For `λ ∈ k^×` let
   `b_q(λ) = dim_k H_q(C_*(T̃; k) ⊗_{k[t^{±1}]} k_λ)`, where `t` acts on `k_λ`
   by `λ`; so `b_q(1) = dim_k H_q(T; k)`. If `T` is a wedge of spheres, then
   `b_q(λ) = b_q(1)` for all `q ≥ 2` and all `λ ∈ k^×`, and `b_1(λ) = b_1(1) − 1`
   for all `λ ≠ 1`. Any violation certifies that `T` is not homotopy equivalent
   to a wedge of spheres.

For a planar Rips complex `T = R_r(X)`, every point `p` outside the shadow
gives such a covering: pull back `R → S^1` along `|T| → S(X; r) ⊆ R^2 ∖ {p} → S^1`.
The simplicial chain complex of the cover has boundary coefficients `±t^{c}`
with `c ∈ {−1, 0, 1}`, read off from the angles of vertices around `p`. The
covering is connected exactly when some edge loop of `T` has total sheet shift
`±1`, i.e. when the winding homomorphism `π_1(T) → Z` is onto.

## Attempts

- Proof in the companion route `wedges-of-spheres-have-free-cyclic-cover-homology-proof`.
