---
rg: 2
id: finite-precision-lifted-trace-proof
kind: route
title: Lift through the nilpotent coefficient ideal and bound the numerator of the regular rank
target: finite-precision-lifted-trace-obstruction
requires: []
artifacts:
  - research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md
---

Sections 1--3 of the artifact give a complete proof. The defect identity
for 3a^2-2a^3 doubles the p-divisibility at each step. Idempotent lifts
of the same reduction are conjugate by E'E+(1-E')(1-E), and projective
equivalences lift through the nilpotent ideal p(Z/p^k)[G]. Cyclicity of
the coefficient trace then gives lift independence, equivalence invariance,
additivity, and the zero trace of every reverse-product defect.

For a finite subgroup H, lift inside Z_p[H] and use the finite regular
representation: its image rank d gives trace d/|H|. Integrality forces
p^(v_p(|H|)) to divide d. The remaining positive numerator is at most
n |H|/p^(v_p(|H|)), so a modulus exceeding that bound detects it.

The proof does not assume soficity or any group approximation. Its
nonvanishing conclusion has the stated finite-subgroup support hypothesis.
