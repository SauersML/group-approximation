---
rg: 2
id: periodic-higman-spectrum-is-cofinite-proof
kind: route
title: Reduce the algebraic matrices at primitive ideal divisors
target: periodic-higman-spectrum-is-cofinite
requires:
  - periodic-higman-algebraic-matrix-certificate
  - voutier-degree-ten-unit-primitive-divisors
artifacts:
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
---

Section 4 of the artifact proves the implication. At a primitive ideal
divisor of `lambda^n-1`, the unit reduces to exact order `n`. Such a prime
is not above two, so all denominators in the certificate remain invertible.
Reduce the four matrices and the diagonal conjugator over the finite
residue field. Conjugation preserves the generated finite subgroup and
therefore acts on it as an automorphism. The nonzero upper-right entry of
the first generator forces this automorphism to have order exactly `n`.
The four upper-right entries also ensure that each base generator survives.
