---
rg: 2
id: natural-compressor-extension-fails-at-toeplitz-commutator
kind: claim
title: Exact finitary block structure forces the truncated shift pair, and the Toeplitz commutator then fails by one transvection
distinct_from:
  toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models: that kills models whose value at x_12(1 − s0 t0) factors through a directly finite coefficient ring; this is a group-level forcing theorem in GL_3N(F_2), where exact finitary conjugation relations determine the images of x_12(t0), x_23(s0), x_13(1), and [x_12(t0), x_23(s0)] = x_13(1) then fails by a transvection.
  transvection-displacement-forces-exact-local-embedding: that shows every relator error is fatal once transvections displace a positive fraction; this computes the one error that the natural level assignment is forced into when it is exact on the whole finitary compressor system, namely the transvection u_13(N−1, N−1) at the Toeplitz commutator.
artifacts:
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

**ESTABLISHED** (proof: Section 2 of the linked artifact, route
`natural-compressor-extension-toeplitz-proof`).

**Setting.**
* `R = L_(F_2)(1,2)`, `e_ab = s0^a (1 − s0 t0) t0^b`.
* `W_N = F_2^N ⊕ F_2^N ⊕ F_2^N`, with `x_ij(e_ab)` sent to the transvection
  `u_ij(a,b) = 1 + δ_a^(i) ⊗ δ_b^(j)*` for `a, b < N`.
* `X = x_12(t0)`, `Y = x_23(s0)`, `Z = x_13(1)`.

**Theorem.** In `GL(W_N)`, the Steinberg relations
* `[X, x_23(e_ab)] = x_13(t0 e_ab)`,
* `[x_12(e_ab), Y] = x_13(e_ab s0)`,
* `[x_21(e_ab), Z] = x_23(e_ab)`,
* and the commutations of `X, Y, Z` with the finitary root elements they commute with in `R^x`,

for all `a, b < N`, have exactly one solution. It is `X^ = 1 + T_N E_12`, `Y^ = 1 + S_N E_23` and
`Z^ = 1 + E_13`, with truncated shifts `T_N δ_0 = 0` and `S_N δ_(N−1) = 0`. For it,
`Z^^(−1)[X^, Y^] = u_13(N−1, N−1)`, a transvection. So the full system, including
`[X, Y] = Z = x_13(t0 s0)`, has no solution in `GL_(3N)(F_2)`.

**Corollary.** Let `σ = lim_ω π_k ∘ τ_k` be a characteristic-two rank model of `R^x`, where `τ_k`
follows the natural assignment, is exact on that system at level `N_k`, and `π_k` is any
representation.
* `u_13(N_k−1, N_k−1)` is conjugate to `u_13(0,0)` in `GL(W_(N_k))`, by swapping indices `0` and `N_k − 1`.
* So the Toeplitz commutator fails by `rk(π_k(u_13(0,0)) − 1)/n_k -> rk(σ(x_13(1 − s0 t0)) − 1)`.
* That limit is positive for nontrivial `σ` (`binary-leavitt-unit-group-is-simple`), so `σ` is
  trivial.

This is the explicit first relation that forces rank for the natural extension over the compressor
pair. It is the Steinberg form of the Toeplitz relation `t0 s0 = 1`. By
`transvection-displacement-forces-exact-local-embedding`, moving the error elsewhere does not help
either: any nontrivial relator error is fatal once one fixed element goes to a transvection.
