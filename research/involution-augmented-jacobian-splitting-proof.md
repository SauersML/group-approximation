---
rg: 2
id: involution-augmented-jacobian-splitting-proof
kind: route
title: Split perturbations into reflection-normal and tangent gradings
target: involution-augmented-code-jacobian-adds-no-cb-loss
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
  - complete-overlay-row-newton-is-a-code-riesz-multiplier
  - aggregate-cut-compression-stores-boundary-as-involution-defect
---

Conjugation by `S_i` is an involution on the selfadjoint Hilbert--Schmidt
space.  Its plus and minus spectral projections give `(IAJ1)`.  Direct
expansion proves `(IAJ2)`, and compatible involution residuals commute with
`S_i`; hence `(IAJ3)` is selfadjoint and is a right inverse.  Multiplication
by the unitary `S_i` preserves every amplified row and column norm, proving
`(IAJ4)`.

Order the augmented Jacobian with the involution equations first.  Relative
to `h=h^+ +h^-` it is block triangular: the first row is `(N,0)`, where
`N` has inverse `(IAJ3)`, and the remaining presentation derivative is
`(D_+,D_-)`.  Fixed word length and balanced normalization bound `D_+` by
a constant `C_0`; the complete-pair derivative is a normalized sum of left
and right unitary multiplications and has the same property.  Solve the
first row, subtract `D_+h^+`, and apply the assumed tangent inverse to
`D_-`.  The triangle inequality gives `(IAJ5)`.

Finally, for a selfadjoint contraction the scalar inequality
`(sgn(lambda)-lambda)^2<=1-lambda^2` gives `(IAJ6)` after functional
calculus.  Telescoping a fixed-width word through contractions and
reflections transfers the vanishing displacement to every relator.
