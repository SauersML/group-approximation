---
rg: 2
id: toeplitz-defect-heisenberg-cells-proof
kind: route
title: Multiply orthogonal defect coefficients through one Steinberg root triangle
target: toeplitz-defect-roots-form-independent-heisenberg-cells
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
---

The Toeplitz equations give pairwise orthogonal nonzero idempotents `e_n`.
Steinberg additivity makes every displayed root have exponent `p`. The root
commutator formula gives `Z_n` on the diagonal and the identity off the
diagonal. Roots with nonmatching index patterns commute, so different cells
commute completely. Linear independence of the coefficients and injectivity
of each Steinberg root map make the centers independent. The standard finite
Heisenberg character table then gives the divisibility `p^r` on a fiber with
`r` active central characters.
