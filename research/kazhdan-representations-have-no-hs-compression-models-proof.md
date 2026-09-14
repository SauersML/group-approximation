---
rg: 2
id: kazhdan-representations-have-no-hs-compression-models-proof
kind: route
title: A small compression defect makes P almost invariant, and the Kazhdan corner lemma then gives a finite-dimensional subrepresentation
target: kazhdan-representations-have-no-hs-compression-models
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
---

Suppose `max_s || C(s)C(s^(-1)) - P ||_(2,d) <= epsilon < epsilon_0`.

1. Since `C(s^(-1)) = C(s)^*`, `Y_s = P - C(s)C(s)^* = P pi(s)(1-P) pi(s)^* P` is positive with `||Y_s|| <= 1`.
   Also `Tr Y_s = || P pi(s)(1-P) ||_HS^2`. By Cauchy–Schwarz, `Tr Y_s <= d^(1/2) || Y_s ||_HS <= epsilon d`.
2. `|| (1-P) pi(s) P ||_HS = || P pi(s^(-1)) (1-P) ||_HS`, and `S = S^(-1)`. So
   `|| [pi(s), P] ||_HS^2 = || (1-P)pi(s)P ||_HS^2 + || P pi(s)(1-P) ||_HS^2 <= 2 epsilon d` for every `s` in `S`.
3. Put `eta = (2 epsilon)^(1/2)`. Since `epsilon < 1/968`, `eta < 1/22`, so (KA1) of
   `kazhdan-almost-invariant-corner-near-invariant-projection` holds. It gives a projection `E` commuting with
   `pi(Gamma)` of finite rank `d'` with `|d' - d| <= (121/kappa^2) eta^2 d < d`, the last inequality because
   `epsilon < kappa^2/242`.
4. So `E != 0`, and `pi` restricted to `ran E` is a nonzero finite-dimensional subrepresentation, contradicting the
   hypothesis.

**Firewall statement.** A finite-dimensional unitary representation of a finitely generated group has residually
finite image by Mal'cev, so for an infinite simple group it is trivial. Then a subrepresentation of a representation
without invariant vectors cannot be finite-dimensional.
