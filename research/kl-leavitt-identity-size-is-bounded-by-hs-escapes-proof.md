---
rg: 2
id: kl-leavitt-identity-size-is-bounded-by-hs-escapes-proof
kind: route
title: Solve the equation exactly with a matrix root and telescope the old relators
target: kl-leavitt-identity-size-is-bounded-by-hs-escapes
requires: [nonsingular-equations-preserve-matrix-certificates]
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

Let `<S | R>` be any presentation of `R^x`.  A death
`a in <<w>>_(R^x * <t>)` lifts to `F(S) * <t>`.  There the defect between the
lift and a product of `w`-conjugates lies in `<<R>>`, and one element of a
normal closure is a finite product of conjugates of finitely many generating
relators.  This gives the displayed identity with finitely many occurring
relators.

For `U in U(d)^S`, the coefficients of `w` evaluate to unitaries, and by
`nonsingular-equations-preserve-matrix-certificates` there is `T in U(d)`
with `w(U, T) = I` exactly.  Evaluating the identity at `(U, T)` removes the
`B` equation factors.  The remaining `A` factors are unitary conjugates of
`r(U)^(+-1)`, and the telescoping inequality
`||X_1 ... X_A - I||_2 <= sum_j ||X_j - I||_2`, together with unitary
invariance of the normalized HS norm, gives (KS1).  This is equation (12) of
the artifact.  No finite-presentation input is used.
