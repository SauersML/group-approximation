---
rg: 2
id: measure-conjugacy-invariants-inert-proof
kind: route
title: An injective automaton is a conjugacy onto its image, so invariants of the image action equal those of the Bernoulli action
target: measure-conjugacy-invariants-cannot-certify-surjectivity
requires: []
artifacts:
  - research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md
---

Section 1 of the artifact.
- A continuous injective equivariant map of the compact space `A^G` is a homeomorphism onto its
  closed image. So `tau` is a topological conjugacy onto `tau(A^G)`.
- Pushing `mu` forward gives an isomorphism of the measure-preserving actions, and the decoder
  gives the continuous inverse on the image.
- Any isomorphism invariant therefore takes equal values on the two actions.
- Corollary 1.2: a property separating the uniform measure from every strict image cannot be an
  isomorphism invariant.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 2.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Scope correction to the last bullet: an isomorphism-invariant property cannot separate the uniform measure from any strict image; for such a property, separation from every strict image is equivalent to the nonexistence of strict automata.
