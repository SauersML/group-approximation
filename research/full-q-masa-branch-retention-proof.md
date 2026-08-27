---
rg: 2
id: full-q-masa-branch-retention-proof
kind: route
title: Use packet normal form and the sectorwise inverse-column corrections
target: full-q-masa-forgets-selectors-retains-branches
requires:
  - raw-schur-generator-is-not-child-center
  - schur-complement-controls-relative-pauli-module
  - oriented-schur-child-branching-identity
---

All `q` generators are commuting involutions and commute with `J`, proving
that `K_f` is elementary abelian.  In the normal form of the class-two packet,
a product of `q` generators has a nonzero `q` coordinate unless that product
is the identity.  Products of `q` generators create no selector coordinate,
because the `q` family commutes internally.  Hence an element of `K_f` lying
in the central selector subgroup can only be `1` or `J`, proving `(QMR2)`.

Equation `(RSC2)` gives `(QMR3)` for every `x`, and this word uses only the
generators displayed in `(QMR1)`.  On sector `x`, `(SCP5)--(SCP7)` show that
`Q_x` commutes with the baseline full matrix algebra and is the corrected
central sign of the `Q` child.  Therefore it acts by opposite scalars on the
two child simples in `(OCB1)`.  If a `K_f` character occurred in both
restrictions, it would assign one value to the same group element `Q_x`,
contradicting those opposite scalars.  Their `K_f` character supports are
therefore disjoint.

The proof uses all sectorwise words simultaneously but never forms the
nonlinear additive coefficient `sum_x e_xQ_x`.  It consequently evades both
the scalar-word affine barrier and the selector-center intersection failure.
