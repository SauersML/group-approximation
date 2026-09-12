---
rg: 2
id: asymmetric-evaluation-separates-opposite-relators-proof
kind: route
title: Kill one inverse-coordinate word and retain the other in a finite elementary group
target: one-opposite-steinberg-relator-does-not-close-laurent-cycle
requires:
  - farey-tree-lift-hits-opposite-steinberg-cycle
---

Write `y_i=x_i^(-1)` when it is regarded as a polynomial generator of
`R_-`.  Define two unital ring maps to the coefficient field `k` by

```text
phi_+:R_+ -> k,       phi_+(x_1)=1, phi_+(x_2)=1,
phi_-:R_- -> k,       phi_-(y_1)=1, phi_-(y_2)=0,              (AER1)
```

and send every `x_j`, `j>=3`, to zero in both maps.  Their restrictions
to

```text
R_0=k[x_3,...,x_d]
```

are equal.  Entrywise application therefore induces homomorphisms

```text
Gamma_+ -> EL_r(k),       Gamma_- -> EL_r(k)
```

which agree on `Gamma_0`.  The universal property of the amalgam gives

```text
rho_0:H=Gamma_+ *_(Gamma_0) Gamma_- -> EL_r(k).                (AER2)
```

For the first coordinate, the elementary commutator formula gives

```text
rho_0(w_1)
 =[e_12(1),e_23(1)]e_13(-1)
 =e_13(1)e_13(-1)
 =1.                                                           (AER3)
```

Thus `rho_0` factors through `H/<<w_1>>`.  For the second coordinate,

```text
rho_0(w_2)
 =[e_12(1),e_23(0)]e_13(-1)
 =e_13(-1)
 !=1.                                                          (AER4)
```

The last inequality holds over every finite field, including characteristic
two: `-1=1` there, but `I+E_13` is still not the identity matrix.
Equation (AER4) proves `w_2 notin <<w_1>>` and supplies the finite
homomorphism asserted in the claim.

Let `lambda` be the left regular representation of the finite group
`EL_r(k)`.  Every nonidentity group element has normalized trace zero, so
(AER4) gives

```text
tr(lambda(rho_0(w_2)))=0,
||lambda(rho_0(w_2))-1||_2^2
 =2-2 Re tr(lambda(rho_0(w_2)))=2.                            (AER5)
```

All vertex relations and the first cross-cone relation hold exactly in this
finite model.  Hence no rigidity statement using only that packet can force
the second relation even approximately.
