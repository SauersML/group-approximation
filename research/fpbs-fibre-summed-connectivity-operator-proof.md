---
rg: 2
id: fpbs-fibre-summed-connectivity-operator-proof
kind: route
title: Schur's test on fibre blocks and weak containment of the quasi-regular representation
target: fpbs-fibre-summed-connectivity-operator
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Theorem 1.1 of the artifact.

* **Inequality.** For finitely supported `f`, `g` on `Gamma`, put
  `F(q) = ||f|_q||_2` and `G(q) = ||g|_q||_2`. Normality gives
  `sum_{v in q'} tau_p(u,v) = sigma_p(q^(-1) q')` for every `u in q`, and
  symmetry of `tau_p` gives the same column sums. Schur's test bounds each block
  by `sigma_p(q^(-1)q')`, so `|<f,T_p g>| <= <F,S_p G>`.
* **Equality for amenable `H`.** `T_p` is the right regular representation of
  `tau_p(o,.)`, and `S_p` is the quasi-regular representation of the same
  function. Amenability gives `lambda_(Gamma/H) = Ind 1_H`, weakly contained in
  `Ind lambda_H = lambda_Gamma`. So the quotient norm is at most the regular
  norm on truncations. Monotone limits finish the proof.
