---
rg: 2
id: matricial-stability-identifies-radicals-proof
kind: route
title: Lift corona coordinates to genuine representations and pass to the limit
target: matricial-stability-identifies-radicals
requires: []
artifacts:
  - GroupApproximation/Sofic/MatricialStabilityRadical.lean
---

## Direct proof

`Rad_MF <= Rad_fd`, no stability needed: given a finite-dimensional unitary
representation `pi`, the constant sequence at `pi` is a corona
representation of `G` (dimensions constant), and an element maps to `1` in
the corona iff `‖pi(g) - 1‖ = 0` iff `g in ker(pi)`.  So
`Rad_MF(G) <= ker(pi)`; intersect over `pi`.

`Rad_fd <= Rad_MF` from stability: let `x in Rad_fd(G)` and let `Theta` be
any corona representation, with coordinate lifts `phi_n : G -> U(k_n)`.  By
the coordinate conventions (`countable-group-mf-conventions`) the lifts
form a point-norm asymptotic homomorphism — for each pair `g, h`,
`‖phi_n(g) phi_n(h) - phi_n(gh)‖ -> 0` — which is exactly the input of
Dadarlat's definition, quantified over arbitrary dimension sequences.
Stability supplies genuine homomorphisms `pi_n : G -> U(k_n)` with
`‖phi_n(s) - pi_n(s)‖ -> 0` for each `s`.  Each `pi_n` is a genuine
finite-dimensional unitary representation, so `pi_n(x) = 1`.  Hence
`‖phi_n(x) - 1‖ -> 0`, i.e. `Theta(x) = 1`.  Every corona representation
kills `x`, so `x in Rad_MF(G)`.

The `Rad_fd(G) = G` case (minimal almost periodicity) recovers
`map-matricial-stability-non-mf`.

## Formalized

`GroupApproximation/Sofic/MatricialStabilityRadical.lean`:
`IsPointNormMatriciallyStable`, `fdUnitaryResidual`,
`actualCoronaMFResidual_le_fdUnitaryResidual` (no stability needed),
`fdUnitaryResidual_le_coronaMFResidual` (stability),
`actualCoronaMFResidual_eq_fdUnitaryResidual`, and
`not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot`.  Authored in the
2026-08-15 generalization wave; the wave's closing validation build
certifies the kernel check.
