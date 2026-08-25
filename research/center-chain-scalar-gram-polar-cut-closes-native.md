---
rg: 2
id: center-chain-scalar-gram-polar-cut-closes-native
kind: route
title: Apply the established scalar-Gram polar cut to the center-chain character atom
target: binary-leavitt-native-two-scale-cross-gram-positive
requires:
  - center-chain-character-atom-gives-scalar-gram
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
---

**INVALIDATED PROPOSAL.**  Feed the exact scalar cross-Gram on the
center-chain character atom directly into the established polar-cut theorem,
then use the resulting common corner as the reducing carrier for both native
Pauli arms.

`center-chain-scalar-gram-polar-cut-returns-moving-atom` computes that this
polar cut is exactly the original atom.  Its two Pauli arm commutator defects
are fixed and nonzero, so the theorem cannot manufacture the missing reducing
subcorner.  A successful route must instead analyze a genuinely different
spectral object, such as the moving-arm Hecke compressions, and prove its
support typing and covariance rather than reusing the scalar-Gram cut.
