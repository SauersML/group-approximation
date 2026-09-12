---
rg: 2
id: fpbs-rd-weighted-bubble-iff-sphere-operator-proof
kind: route
title: Chain rapid decay on spheres, the sphere-cut bootstrap, and summation by parts
target: fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one
requires:
  - fpbs-sphere-cut-fibre-tails-decay-exponentially
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

* **(b) ⟹ (c).** Apply rapid decay to the sphere-supported function
  `sigma_{p_c} 1_{S_Q(R_0)}`, whose l2 norm squared is `b_{R_0}(p_c)`.
* **(c) ⟹ (d), (e).** This is the bootstrap `fpbs-sphere-cut-fibre-tails-decay-exponentially`.
* **(d) ⟹ (e) ⟹ (a).** Summation by parts against polynomial weights.
* **(a) ⟹ (b).** `(1+R)^(2D+2) b_R(p_c) <= W_D(p_c)`, so
  `C^2 (1+R)^(2D) b_R(p_c) -> 0`.
* **Dichotomy.** It is the negation of (b), read against (d).

Full proof: artifact Theorem 3.1.
