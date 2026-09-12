---
rg: 2
id: stw99-lxxvi-nccw-homotopy-fibre-proof
kind: route
title: Read scalar torsion at the zero-skeleton and kill the remaining loop obstruction in pi6
target: stw99-lxxvi-one-dim-nccw-s6-criterion
requires:
  - stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

## Necessity: evaluation detects every scalar vertex

The quotient map

```text
ev_E:A->E,                 (f,a)|->a
```

sends the scalar unitary `u in U(2)` to

```text
(u tensor 1_(r_i))_(i=1)^s in product_i U(2r_i).       (1)
```

If `r_i=1`, the `i`-th component of the image of `alpha` in (1) is the
original nonzero element of `pi_5(U(2))=Z/2`.  Hence the image in
`pi_5(U(M_2(E)))` is nonzero.  A null-homotopy in `U(M_2(A))` would descend
through `ev_E` to a null-homotopy of (1), which is impossible.  Therefore
one scalar zero-skeleton summand forces survival, independently of both
endpoint multiplicity matrices.

## Sufficiency: the only residual obstruction is stable even homotopy

The unitary group of `M_2(A)` is the homotopy equalizer of the induced maps

```text
U(M_2(E)) two arrows U(M_2(F)).                         (2)
```

Equivalently, near the identity component it is the homotopy fibre of the
difference of the two endpoint maps.  Its standard exact homotopy sequence
contains

```text
pi_6(U(M_2(F))) -> pi_5(U(M_2(A)))
 -> pi_5(U(M_2(E))).                                   (3)
```

Assume every `r_i>=2`.  Each component

```text
u |-> u tensor 1_(r_i):U(2)->U(2r_i)
```

kills `alpha` by
`stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class`.  Thus the right-hand
image of `alpha_A` in (3) is zero, and exactness puts `alpha_A` in the image
of `pi_6(U(M_2(F)))`.

Unitality of either endpoint map gives the dimension equations `(M)`.  Since
all `r_i>=2`, every nonzero row has

```text
d_j=sum_i m_(epsilon,j,i)r_i>=2.                       (4)
```

Therefore

```text
pi_6(U(M_2(F)))=directSum_j pi_6(U(2d_j))=0.           (5)
```

Indeed `6<4d_j`, so degree six is already in the stable range, and Bott
periodicity gives `pi_6(U)=0`.  Equations (3)--(5) force `alpha_A=0`.

Finally, any unital embedding `A->D` factors the scalar inclusion through
`A`; functoriality carries the zero class to `pi_5(U(M_2(D)))`.

The proof also explains why the numerical values in `mu_0,mu_1` disappear.
They affect the difference map later in the exact sequence, but the scalar
class has already vanished on every zero-skeleton component and the entire
possible lifting group on the left of (3) is zero.  If a scalar vertex is
present, evaluation detects it before the endpoint maps can act.
