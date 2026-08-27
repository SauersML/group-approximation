---
rg: 2
id: expand-three-unit-defect-and-conjugate-one-s3-packet
kind: route
title: Expand the ten-term lift defect and conjugate the annihilated S3 relation once
target: single-conjugated-s3-packet-correction-equation
requires:
  - leavitt-rank-three-unit-lift
  - leavitt-corner-idempotent-unital-surjection
  - leavitt-evaluation-kernel-hits-augmentation-one
  - compressed-s-rank-three-lift-has-no-one-sided-inverse
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

The self-similarity matrices display nine distinct products `U_iV_j`, all
different from the identity, so `D` has ten terms.  Insert `1=e+(1+e)`
between the two lifts to obtain the formula for `Delta`.  Conjugation keeps
the three-term packet in the evaluation kernel, and multiplication by `e`
puts it in the corner.  Expanding `(A+P_x)B=e` gives exactly the stated
single equation.

That equation would give the fixed `B=e s~e` a left inverse, contradicting
the last prerequisite.  Hence it has no solution for any conjugator.
