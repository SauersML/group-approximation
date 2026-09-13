---
rg: 2
id: dd-toeplitz-algebra-is-properly-infinite-proof
kind: route
title: Proof that T(E_DD) is properly infinite via orthonormal sections of E_DD tensor E_DD
target: dd-toeplitz-algebra-is-properly-infinite
requires: []
artifacts:
  - research/artifacts/lxi-dd-toeplitz-proper-infiniteness-2026-09-12.md
---

Complete derivation in the artifact, sections 2--4.

1. (Lemma 1) If `θ_1, θ_2` in the span of elementary tensors of `E^{⊗k}` satisfy
   `<θ_i,θ_j> = δ_ij`, then `l_k(θ) = l(z_1)...l(z_k)` (extended linearly) lies in `T(E)` and
   `l_k(θ)^* l_k(θ') = <θ,θ'>`. So `l_k(θ_1), l_k(θ_2)` are isometries with orthogonal ranges.
2. (Proposition 2) Let `E = PF`, where `1-P = Σ_{j≤n} θ_{η_j,η_j}` for orthonormal `η_j`, and let
   `e_1..e_{2N}` be orthonormal sections of `F`, with `N = 3n+1`. Put `ζ_k = Pe_k`, so
   `<ζ_k,ζ_l> = δ_kl - M_kl`. Pointwise `M = BB^*` with `0 ≤ M ≤ 1` and `tr M ≤ n` (Bessel). Put
   `V = Σ_{k≤N} ζ_k⊗ζ_k` and `W = Σ_{N<l≤2N} ζ_l⊗ζ_l`. Then
   `<V,V> = N - 2Σ M_kk + tr(M_I conj(M_I)) ≥ N-2n`, likewise `<W,W> ≥ N-2n`, and
   `|<V,W>| ≤ tr(M^2) ≤ n`. Gram--Schmidt with continuous functions gives orthonormal
   `θ_1, θ_2 ∈ E⊗E`.
3. (Theorem 3) For `E_DD = (1-θ_{η,η})F''`, take `n=1`, `η_1 = η` and the constant sections
   `e_k ⊕ 0`, which are orthonormal because `F''` has the pointwise inner product. For `H~`, the
   summand `E_DD ⊗ C((B_3)^∞)` is the same construction pulled back, and it is an orthogonal summand
   of `H~`.
