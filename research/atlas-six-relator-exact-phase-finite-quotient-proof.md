---
rg: 2
id: atlas-six-relator-exact-phase-finite-quotient-proof
kind: route
title: Apply Malcev separation to a positive five-row bridge and regularize a finite quotient
target: atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test
requires:
  - regular-atlas-linearized-h-coercivity
---

Assume first that `(SXFQ1)` holds.  The two regular chart representations
and `U` define a homomorphism

```text
pi:Gamma_6 -> Lambda <= U(20160k).
```

Both chart restrictions are faithful.  The established equality of the
five-row linear kernel with the `H`-covariance kernel shows that positive
linear energy makes at least one standard bridge nonidentity in `Lambda`.
The finitely generated linear group `Lambda` is residually finite by
Malcev's theorem.  Apply residual finiteness simultaneously to

* that nonidentity bridge;
* one fixed nonidentity element of the first `A8`; and
* one fixed nonidentity element of the second `A8`.

Taking the product of the three resulting finite images gives a finite
quotient of `Gamma_6` in which the bridge survives and neither chart image
is trivial.  Simplicity of `A8` makes both chart restrictions injective.

Conversely, suppose `Gamma_6 -> F` has the properties in condition 2.  In
the left regular representation of `F`, either chart restricts to
`[F:A8] Reg(A8)`.  Choose a unitary identifying the second restriction with
the fixed model of the first.  Every defining relator is then exactly one,
so all six nonlinear defects vanish.  A surviving standard bridge has
positive normalized-HS distance from the identity in `Reg(F)`, hence the
`H`-covariance energy is positive.  The fixed five-row kernel/coercivity
theorem forces the five-row linear energy to be positive.  This proves
`(SXFQ1)` and `(SXFQ2)`.

