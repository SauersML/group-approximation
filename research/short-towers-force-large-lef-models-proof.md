---
rg: 2
id: short-towers-force-large-lef-models-proof
kind: route
title: Proof via the tower copy of GL_d(F_2) and detection of U_d(F_2) by its central transvection
target: short-towers-force-large-lef-models
requires: []
artifacts: [research/artifacts/sk-lef-growth-bounds-2026-09-13-part1.md, research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md]
---

The complete derivation is sk-lef-growth-bounds part 1 (Lemmas 0–1) and part 2 (Lemma 3, Lemma 4, Theorem C):

1. **Lemma 0.** An injective partial homomorphism φ of B(r) satisfies φ(s_1⋯s_ℓ) = φ(s_1)⋯φ(s_ℓ) for ℓ ≤ r. So relations of length ≤ r transport.
2. **Lemma 1.** |e_ij(u^a r u^b)| ≤ |e_ij(r)| + 12(|a|+|b|), by conjugating with the length-6 Whitehead elements diag(u, u^{-1}, 1).
3. **Lemma 4.** E_ab(W) = u^a e_W u^{-b} (|a|, |b| ≤ m) are matrix units because the levels T^aW are disjoint. So GL_d(F_2) embeds in G_X, and every elementary transvection τ_PQ is e_pq(E_ab(W)) or a commutator of two of these. Each has length ≤ λ = 4(κ + 24m).
4. **Lemma 3.** Involutions y_PQ satisfying the Steinberg relations of U_d(F_2) define a homomorphism from U_d(F_2), which is injective as soon as y_1d ≠ 1.
5. **Assembly.** The relations have length ≤ 5λ ≤ r, so they transport. φ(τ_1d) ≠ 1 by injectivity. So |Q| ≥ |U_d(F_2)| = 2^{d(d−1)/2}.
