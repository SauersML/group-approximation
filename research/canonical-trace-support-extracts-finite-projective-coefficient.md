---
rg: 2
id: canonical-trace-support-extracts-finite-projective-coefficient
kind: route
title: Extract a finite projective coefficient from the canonical trace support
target: odd-maslov-homogeneous-split-ucp-retract-is-impossible
requires:
  - finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres
---

Schwarz equality puts every homogeneous generator image in the
multiplicative domain of the split retraction.  Compose the coefficient
corner with the canonical twisted trace and let `p` be the support of the
resulting matrix state.  Multiplicative-domain covariance and the two
positive Schwarz defects make `p` reduce every coefficient contraction and
make its restriction unitary.

Apply the same multiplicative-domain argument to the difference between a
product of two generator images and the image of the twisted product.  Its
positive square is killed by the retraction, hence by the supported matrix
state.  The restricted coefficient unitaries therefore obey the exact
difference-multiplier law.  Their support is nonzero, producing the forbidden
finite-dimensional odd-Maslov projective representation.
