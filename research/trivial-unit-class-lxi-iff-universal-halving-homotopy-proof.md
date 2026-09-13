---
rg: 2
id: trivial-unit-class-lxi-iff-universal-halving-homotopy-proof
kind: route
title: Proof of the halving-homotopy equivalence through the universal property of O_2 * C(T)
target: trivial-unit-class-lxi-iff-universal-halving-homotopy
requires: []
artifacts:
  - research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md
---

Artifact, Theorem 2 and Remark 3.

- (3 ⇒ 1) `U ⊇ O_2` unitally, so `U` is properly infinite and `[1_U] = 0`.
- (1 ⇒ 2) `[C(z)] = [Θ(diag(z,1))] = [z]` in `K_1(U)`, so `z^* C(z)` is K1-trivial, hence null by (1). Push
  it forward along `U → A`, `s_i ↦ s_i`, `z ↦ w`.
- (2 ⇒ 3) Since `[1_A] = 0` and 1 is properly infinite, `1⊕1 ~ 1` (Cuntz), which gives a Cuntz pair. For
  `[u] = 0`, BRR Lemma 2.4(ii) gives `diag(u,1) ∈ U_0(M_2(A))`. The isomorphism
  `Θ: M_2(A) → A` then gives `C(u) ∈ U_0(A)`, and by (2), `u ~_h C(u)`.
- (Remark 3) The maps `ι_1(s_k) ↦ s_k`, `ι_2(s_k) ↦ zs_k` and `z ↦ Σ_l ι_2(s_l)ι_1(s_l)^*`,
  `s_k ↦ ι_1(s_k)` are mutually inverse. This is Blanchard arXiv:0804.4624 Proposition 4.6(i) with 2 in
  place of 3.
