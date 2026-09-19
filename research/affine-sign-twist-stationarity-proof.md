---
rg: 2
id: affine-sign-twist-stationarity-proof
kind: route
title: Restrict the S3 sign to the active little group and compute the two-cycle
target: affine-sign-twist-swaps-active-blocks-but-is-stationary
requires:
  - affine-s3-active-idempotent-toeplitz-envelope
---

Clifford theory for `D normal C_aff` identifies irreducibles above the active
three-point orbit with irreducibles of a point stabilizer `H~=C_2`.  They are

```text
pi_+=Ind_(D semidirect H)^C_aff(psi tensor 1),
pi_-=Ind_(D semidirect H)^C_aff(psi tensor sgn_H).
```

The quotient sign restricts to `sgn_H`, so tensoring by it exchanges `pi_+`
and `pi_-`.  Duality between irreducible characters and primitive central
idempotents proves `(AST3)`.

Because `Theta_chi(A)=A`, the coefficient twist extends to `R_aff` by fixing
`x,y`.  The packet-headed Toeplitz formula tolerates this automorphism before
the corner map; it does not require the automorphism to preserve the chosen
augmentation.  Expanding `(AST4)`, the cross terms vanish by `Ax=0` and
`yA=0`, while `yx=1` handles the main term, multiplicativity of `epsilon`
handles the scalar term, and `xy+A=1` gives unitality.  Multiplying on the
left by `y` and on the right by `x` recovers `Theta_chi(a)`, so applying
`Theta_chi^-1` proves injectivity.  Since the augmentation vanishes on both
active blocks, `(AST5)` follows.  Its multiplicity matrix is `(AST6)`, which
has eigenvalues `1` and `-1`; hence neither active direction contracts.
