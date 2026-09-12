---
rg: 2
id: kraus-projection-and-haar-commutators-control-masa-rounding
kind: route
title: Project Kraus operators to a maximal abelian algebra and test the native noncommuting pair
target: near-fixed-masas-round-channels-but-exclude-native-heat
requires:
  - schur-near-idempotents-round-dimension-uniformly
  - finite-leavitt-core-averages-stay-far-from-kazhdan-heat
  - property-t-laplacian-sos-certificate
artifacts:
  - research/artifacts/masa-channel-rounding-and-native-heat-separation-2026-09-08.md
---

Project each Kraus operator of `P` onto `D`. The sum of squared
normalized-HS changes is exactly the averaged `D`-energy `a`.
The resulting diagonal Kraus operators have a positive diagonal
unitality deficit. Add its square root as one more Kraus operator.
The repaired map is Schur and bistochastic. Self-adjointness of `P`
makes its Schur coefficients real. Comparing the two Stinespring
isometries costs at most `2 sqrt(2a)` in infinity-to-two norm.
Composition transfers near idempotence with a further factor three,
and the exact Schur theorem supplies a block expectation.

For the native limitation, suppose a channel `S` fixes some ambient
maximal abelian `D` pointwise and is close to a heat map `P`.
Every unitary in `D` then has small commutators with the two chosen
native word matrices, because the heat outputs do. Haar averaging
places both word matrices close to `D`. Their diagonal expectations
commute and are contractions, bounding the original commutator.
Canonicality makes the norm of that nontrivial commutator tend to
`sqrt(2)`. This gives distance at least `1/4` from every Schur channel.

For the averaged-energy version, positivity `0<=P<=I` on the
Hilbert space gives `(I-P)^2<=I-P`. The same Haar calculation yields
the lower bound `1/16` without any uniform near-fix assumption.
The heat-output commutator estimates follow directly by evaluating a
fixed Kazhdan SOS certificate on bounded matrices and integrating the
resulting energy inequality. No finite-coordinate spectral gap or
conditional-expectation rounding is assumed.
