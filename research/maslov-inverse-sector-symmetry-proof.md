---
rg: 2
id: maslov-inverse-sector-symmetry-proof
kind: route
title: Anti-symplectic conjugation reverses the fundamental-group generator
target: maslov-inverse-sector-symmetry
requires: []
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Write the standard symplectic form as

```text
J = [ 0  I ; -I  0 ]
```

and put `D=diag(I_2,-I_2)`.  Then `D^T J D=-J`, so conjugation
`theta(A)=DAD^{-1}` normalizes `Sp_4(Z)` and extends to an automorphism of
`Sp_4(R)`.

The maximal compact `U(2) <= Sp_4(R)` consists of real block matrices
corresponding to complex unitary matrices `A+iB`.  Conjugation by `D` sends
`A+iB` to `A-iB`, i.e. complex conjugation.  Under

```text
pi_1(U(2)) ~= pi_1(Sp_4(R)) ~= Z,
```

the determinant winding generates `pi_1`, and complex conjugation reverses
that winding.  Thus `theta_*` acts by `-1` on the deck group of the universal
cover.  The lifted automorphism sends a deck generator `t` to `t^{-1}` and,
after quotienting by `3Z`, sends the central generator of the connected
three-fold cover to its inverse.

Restricting to the inverse image of `Sp_4(Z)` proves `(MIS1)`.  Precomposition
by `theta` preserves every normalized-HS relator defect after transporting the
finite presentation, so the two nontrivial projective sectors have identical
defect infima.
