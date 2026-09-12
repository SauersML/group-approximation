---
rg: 2
id: stw50-bott-and-rotation-unit-citation
kind: route
title: Import stable Bott evaluation and compute the split rotation unit by the PV sequence
target: stw50-bott-and-rotation-unit-inputs
requires: []
artifacts:
  - research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md
---

Use Bott periodicity with the scalar loop as the positive unit
generator, as in STW Section 14, equation (15).

Apply the Pimsner--Voiculescu exact sequence to circle rotation.
Rotation is homotopic to the identity, so both 1-sigma_* maps vanish.
This gives the stated short exact sequence. Lift 1 in its quotient
Z to q; then every element is uniquely m[1]+nq, and sending it to m
is the required retraction. The O_infinity K-theory identification is
the one in STW Section 14. Abelianity of pi_1 of a topological group
follows from the interchange law for loop concatenation and pointwise
multiplication.
