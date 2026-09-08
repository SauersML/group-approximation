---
rg: 2
id: primary-mass-gap-from-kirillov-and-tensor-powers
kind: route
title: Use positive orbit measures to exclude escaping conductor mass and amplify a failed quadratic bound
target: sl3-primary-mass-has-a-uniform-quadratic-gap
requires:
  - sl3-primary-exact-congruence-mass-vanishes-at-every-prime
artifacts:
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
  - research/artifacts/sl3-primary-mass-quadratic-amplification-2026-09-08.md
---

The prerequisite, proved in the first artifact, supplies the qualitative statement: for exact
congruence representations, vanishing fixed-overlap intertwining defect
forces the whole denominator-primary mass to vanish. It includes the
prime-two restriction-to-squares correction, the Chinese remainder
precision after conjugation, the limiting coupling at projective
infinity, and the passage from Fourier tightness to invariant dimension.

The second artifact upgrades that statement to `(PQG)`. Project a
unitary onto the exact overlap intertwiner space and extract its
primary restriction. If `q/epsilon^2` were unbounded, add a trivial
summand, tensor with the conjugate, and take `ceil(1/q)` tensor powers.
The transformed overlap residuals have nonnegative real traces, so
their squared defects grow at most linearly in the tensor exponent.
The fixed Kazhdan displacement of a lattice generator is amplified to
a positive constant. This contradicts the first artifact's qualitative
mass-vanishing theorem for the resulting pure-primary representations.

Both artifacts give written proofs; this route asserts no new Lean
kernel certification.
