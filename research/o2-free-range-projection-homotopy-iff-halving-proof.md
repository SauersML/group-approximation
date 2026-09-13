---
rg: 2
id: o2-free-range-projection-homotopy-iff-halving-proof
kind: route
title: Adapt the Blanchard-Rohde-Rordam projection criteria to Cuntz pairs with trivial unit class
target: o2-free-range-projection-homotopy-iff-halving
requires: []
artifacts:
  - research/artifacts/k1-halving-projection-form-2026-09-13.md
---

Complete proof in the artifact (Theorem 1, Propositions 2 and 3). It uses only BRR Proposition 2.3,
Lemma 2.4(ii) and Proposition 5.1, verified against arXiv:0704.1554v1, together with Blanchard's
isomorphism `O_2 * O_2 ≅ O_2 * C(T)` and `K_1(O_2 * C(T)) = Z`, from Germain's six-term sequence.

- (1) => (2): BRR Proposition 5.1 (i) => (ii), applied to `e_1 = s_1s_1^*` and `e_2 = z e_1 z^*`. All four
  of `e_1, e_2, 1 - e_1, 1 - e_2` are equivalent to 1.
- (2) => (1): let A be properly infinite with `[1] = 0`, and p, q properly infinite and full. Choose
  `p_0 <= p` and `q_0 <= q` equivalent to 1, with properly infinite full complements. Then `1 - p_0 ~ 1`
  (BRR 2.3), so `p_0` and `q_0` are ranges of first isometries of Cuntz pairs. That gives a unital map
  `D -> A` sending `iota_1(s_1s_1^*) -> p_0` and `iota_2(s_1s_1^*) -> q_0`. BRR 5.1 (iii) => (i) finishes.
- (2) <=> (3): nontrivial projections of `O_2` are unitarily equivalent to `s_1 s_1^*`, and `U(O_2)` is connected.
- (3) <=> (4): BRR Proposition 4.3, (i) <=> (ii).
- Halving map: `C(C(w)) C(w)^* = C(C(w)w^*)` commutes with `s_1s_1^*` and is K1-trivial, so it is null by
  BRR Lemma 2.4(ii).
- Embeddings: Cuntz pairs are a `U(A)`-torsor, and `[z rho(z^*)] = -[z]`.
