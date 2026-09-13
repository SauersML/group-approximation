---
rg: 2
id: u2-quadruple-samelson-eta-cubed-proof
kind: route
title: One more naturality step gives eta cubed, the half-smash splitting detects it on T^3 x S^3, and the excess bound caps the class at four
target: u2-quadruple-samelson-class-four-stage
requires:
  - u2-triple-samelson-class-three-stage
  - block-component-group-class-at-most-excess-plus-two
artifacts:
  - research/artifacts/class-four-stage-and-blind-spin-trapping-2026-09-12.md
---

The first prerequisite gives <alpha, omega> = omega o eta_3, and naturality
<alpha, omega o h> = <alpha, omega> o (1 ∧ h). Taking h = eta_3 o eta_4 gives
omega o eta_3 o eta_4 o eta_5. Toda: eta_3^3 = 6 nu' in pi_6(S^3) = Z/12. It
suspends to eta^3 = 12 nu ≠ 0 in pi_3^s.

The nested commutator is 1 on the fat wedge of T^3 x S^3, so it factors
through the collapse to S^6. Detection works as in the first prerequisite.
The pair {1} x Y ⊂ S^1 x Y, with Y = T^2 x S^3, has a retraction, so
[Sigma(Y_+), U(2)] -> [S^1 x Y, U(2)] is injective. Sigma Y splits off the
summand S^6 = Sigma(S^1 ∧ S^1 ∧ S^3) with a homotopy section of the collapse.
So pi_6 U(2) injects, and the class four lower bound holds.

Upper bound: dim = 6 and rank = 2, so the second prerequisite gives class at
most 2 + 2 = 4.
