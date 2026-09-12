---
rg: 2
id: strict-automata-copy-retract-poset-proof
kind: route
title: Conjugate idempotents by the strict automaton and its left inverse
target: strict-automata-copy-the-retract-poset-below-their-image
requires: []
artifacts:
  - research/artifacts/automaton-monoid-intrinsic-sizes-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Theorem 2.1 and Corollary 2.2 of the artifact.

- **Images are retract images:** `(tau f sigma)^2 = tau f (sigma tau) f sigma = tau f sigma`, and
  `sigma` is surjective because `sigma o tau = id`, so the image is `tau(f(A^G))`.
- **Conjugacy:** `tau` is an injective continuous equivariant map on a compact space, hence a
  homeomorphism onto its image.
- **Onto the down-set:** `e = tau sigma` fixes `tau(A^G)` pointwise, so `e g = g` for any idempotent
  `g` whose image lies in `tau(A^G)`. Then `(sigma g tau)^2 = sigma (e g) g tau = sigma g tau`. Its
  image is `sigma(g(tau(A^G))) = sigma(Y)`, since `g` fixes `Y` and `Y <= tau(A^G)`. Finally
  `tau(sigma(Y)) = e(Y) = Y`.
- **Corollary:** an invariant of the down-set is unchanged under the isomorphism `Phi`, which sends
  `A^G` to `tau(A^G)`.

**Verification.** `w3-vf-positive` passed this route (Section 6.2 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). Typo in artifact Theorem 2.1(3): the middle step should read sigma g (e g) tau; the conclusion is unaffected.
