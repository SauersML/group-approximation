---
rg: 2
id: atlas-l44-frobenius-intertwiner-proof
kind: route
title: Apply twisted Schur descent to the common H6-H18 module
target: atlas-l44-frobenius-intertwiner-prunes-frames
requires:
  - atlas-l44-h6-has-thirty-frobenius-frames
---

# Apply twisted Schur descent to the common H6-H18 module

Subfield containment supplies a Frobenius-semilinear involution commuting
with `J`, hence a nonzero element of `(L44I-1)`. Conversely, twisted Schur's
lemma makes every nonzero element invertible and the ordinary Schur lemma
makes `D D^(2)` scalar. The determinant calculation `(L44I-5)` makes it one,
so Galois descent gives the binary fixed space. Uniqueness follows from the
one-dimensional intertwiner space. For `(L44I-9)`, Frobenius-fixing both
conjugated generating sets puts `c^-1c^(2)` in the certified scalar common
centralizer; solving the resulting entry equation gives a scalar times a
binary matrix.
