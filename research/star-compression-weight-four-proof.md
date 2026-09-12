---
rg: 2
id: star-compression-weight-four-proof
kind: route
title: Haar mass conservation on half the space forces collisions, and F_3 norms force weight four
target: star-compression-designs-need-weight-four-colliding-columns
requires:
  - thompson-action-on-odd-measures-is-essentially-free
artifacts:
  - research/artifacts/odd-measure-star-compression-designs-2026-09-12.md
---

Sections 2 and 4 of the artifact (Lemma 2.1, Theorem 4.1).

* **Norm.** `x* x = eps_-` at the identity component says `sum_g a_g(g mu)^2 = 1`; nonzero squares in
  `F_3` are `1`, so `c(mu) ≡ 1 mod 3`.
* **Mass.** `V`-invariance of Haar measure gives `∫ c = ∫ n`, and `n` is supported on `U_[0]`, of
  measure `1/2`. So `{n >= 2}` carries mass at least `1/2`.
* **Collisions.** Essential freeness makes almost every collision one between distinct columns, which
  are orthogonal by the off-identity components. A single shared point gives a nonzero pairing, so
  they share at least two points, hence `c >= 2`, hence `c >= 4`.
* **Transport.** Counting pairs `(g, mu)` with `g mu` in the collision set bounds that mass by
  `∫_(c >= 4) c`.
