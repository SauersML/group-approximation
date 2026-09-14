---
rg: 2
id: rotation-factor-subshifts-have-linear-cost-towers-proof
kind: route
title: Proof by an arc of length ‖q_nα‖, best approximation, and a letter check at t = ±q_n
target: rotation-factor-subshifts-have-linear-cost-towers
requires: []
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part1.md]
---

Full proof: artifact part 1, Lemma 5 and Theorem R1. Summary for η_n > 0, with η = η_n, q = q_n and θ = π(x):

1. **x ∈ W ⇒ θ ∈ [β' − η, β'].**
   - x_0 = a gives θ ∈ [β, β'].
   - x_q ≠ a gives θ + η ∉ (β, β').
   - Because |I| + η < 1 there is no wrap, so θ + η ≥ β'.
2. **Nonempty.** For θ ∈ (β' − η, β') and x ∈ π^{-1}(θ), the sandwich gives x_0 = a and x_q ≠ a, since θ + η ∉ cl I.
3. **No returns.**
   - x, T^{-t}x ∈ W gives ‖tα‖ ≤ η. Best approximation (for 0 < |t| < q_{n+1}, ‖tα‖ ≥ η with equality only at ±q_n) leaves t = ±q.
   - t = q is impossible: T^{-q}x ∈ W gives x_0 ≠ a.
   - t = −q is impossible: T^qx ∈ W gives x_q = a.
4. **Cost.** e_W = e_a + e_a·u^{-q}e_a u^q, so e_ij(e_W) = e_ij(e_a)[e_ik(e_a), e_kj(u^{-q}e_a u^q)], of length ≤ 1 + 2 + 2(1 + 24q) by `short-towers-force-large-lef-models`' Lemma 1.

The case η_n < 0 is symmetric, with the arc [β, β + |η_n|].
