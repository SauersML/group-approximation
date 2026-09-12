---
rg: 2
id: kl-leavitt-identity-size-is-bounded-by-hs-escapes-proof
kind: route
title: Solve the equation exactly with a matrix root and telescope the old relators
target: kl-leavitt-identity-size-is-bounded-by-hs-escapes
requires: [nonsingular-equations-preserve-matrix-certificates, leavitt-unit-group-finitely-presented]
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

Since `R^x` is finitely presented, `<S | R>` exists, and a death
`a in <<w>>_(R^x * <t>)` lifts to an identity in `F(S) * <t>` in which the
defect between the lift and the product of `w`-conjugates lies in the normal
closure of `R`; one element of a normal closure is a finite product of
conjugates of the generating relators.  This is the displayed identity.

For `U in U(d)^S`, the coefficients of `w` evaluate to unitaries, and by
`nonsingular-equations-preserve-matrix-certificates` there is `T in U(d)`
with `w(U, T) = I` exactly.  Evaluating the identity at `(U, T)` removes the
`B` equation factors.  The remaining `A` factors are unitary conjugates of
`r(U)^(+-1)`, and the telescoping inequality
`||X_1 ... X_A - I||_2 <= sum_j ||X_j - I||_2` with unitary invariance of the
normalized HS norm gives (KS1).  This is equation (12) of the artifact, with
the relator list fixed once and for all.
