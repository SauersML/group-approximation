---
rg: 2
id: uniform-unstable-length-bound-from-lxi
kind: route
title: LXI implies a uniform unstable exponential-length bound, through sequence algebras
target: properly-infinite-unstable-length-uniformly-bounded
requires: [stw99-problem-lxi-properly-infinite-k1-injective]
artifacts:
  - research/artifacts/lxi-uniform-unitary-length-reformulation-2026-09-12.md
---

Suppose the bound fails for some `L`. Choose unital properly infinite `A_n` and `u_n` with
`cel(diag(u_n,1)) ≤ L` and `cel(u_n) > n`. In `Q = l^∞(A_n)/c_0(A_n)`, which is unital and properly
infinite (combine the orthogonal isometries of the `A_n`), put `u = [(u_n)]`.

1. By Lemma A, each `diag(u_n,1)` is a product of `M = floor(2L)+5` exponentials of norm at most
   `max(π, L+1)`, with `M` independent of `n`. These lift, so `diag(u,1) ∈ U_0(M_2(Q))` and `[u] = 0`
   in `K_1(Q)`.
2. By LXI, `u = e^{ih_1}...e^{ih_m}` in `Q`. Lift the `h_t` to bounded self-adjoint sequences. Then
   `u_n` is within distance 1 of `Π_t e^{ih_{t,n}}` for large `n`. So
   `cel(u_n) ≤ π/3 + Σ_t (||h_t|| + 1)`, independent of `n`. This is a contradiction.

Artifact Theorem B, 1 => 2.
