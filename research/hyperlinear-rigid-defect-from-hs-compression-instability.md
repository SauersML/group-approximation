---
rg: 2
id: hyperlinear-rigid-defect-from-hs-compression-instability
kind: route
title: A finite-dimensional compression instability at the Kun--Thom pair generates a hyperlinear group with a nontrivial rigid defect
target: hyperlinear-group-carries-nontrivial-rigid-defect
requires: [hs-compression-stability-fails-at-the-theorem-e-pair, kazhdan-commutant-compression-stability-is-finitary]
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

1. By `kazhdan-commutant-compression-stability-is-finitary` (direction `NORM => UCS`,
   contrapositive), the counterexample sequence of
   `hs-compression-stability-fails-at-the-theorem-e-pair` gives a homomorphism
   `sigma : G -> U(prod_U M_n)` and a unitary `z in C(sigma(Gamma))` with
   `w = sigma(t) z sigma(t)^*` not commuting with some `sigma(s)`, `s in F`, `t in {A,B}`.
2. Put `H = <sigma(G), z>`, a countable subgroup of `U(prod_U M_n)`, hence hyperlinear.
3. `sigma(Gamma) <= sigma(G) <= H` is a rigid pair.
   - Both groups are quotients of Kazhdan groups, hence Kazhdan.
   - `sigma(A), sigma(B)` compress `sigma(Gamma)` and generate `sigma(G)` with it.
4. `z in C_H(sigma(Gamma))`, `sigma(t) in sigma(G)` and `sigma(s) in sigma(Gamma)`. So
   `[sigma(t) z sigma(t)^-1, sigma(s)] != 1` is a nontrivial rigid defect of that pair in `H`.

Then `hyperlinear-nonsofic-via-hyperlinear-rigid-defect` makes `H` nonsofic.
