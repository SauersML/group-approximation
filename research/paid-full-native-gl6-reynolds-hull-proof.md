---
rg: 2
id: paid-full-native-gl6-reynolds-hull-proof
kind: route
title: Reynolds-average the paid contraction over the literal six-summand actor
target: paid-t00-support-enters-full-native-gl6-hull
requires:
  - paid-t00-pauli-menu-hits-whitehead-constant-atom
  - two-native-singers-and-endpoint-generate-literal-gl6
---

The paid Pauli-menu theorem gives `(PGR1)`.  Every element of `G_6`
commutes with `z`, hence with `P`.  Therefore every summand in `(PGR2)` is a
positive contraction supported on `P`, so

```text
0<=B<=P,                 tau(B)=tau(A).                 (1)
```

The average is invariant under conjugation by `G_6`.  Functional calculus
therefore gives

```text
[E,rho(G_6)]=0,               E<=P.                    (2)
```

Since `0<=B<=E`, equations `(1)--(2)` give

```text
tau(E)>=tau(B)=tau(A)>=tau(P)/128>0.                  (3)
```

The identity element occurs in the Reynolds sum, so

```text
B>=(1/|G_6|)A.                                         (4)
```

For positive operators, `(4)` implies `ker(B)<=ker(A)`, equivalently
`supp(A)<=supp(B)=E`.  This proves `(PGR3)--(PGR4)`.

By the literal GL6 theorem, every word in `(NSG3)` belongs to `G_6`.
Equation `(2)` therefore says that `E` reduces `M_1,M_2,J_1,J_2,W` and the
four individual factors `A_1,B_2,A_2,B_3`.  In particular both order-seven
relations and the endpoint order-five relation restrict with zero boundary
to `EH`; no moving-cut telescope is needed on this carrier.

For the stated boundary, the matrices in `(PGR5)` give

```text
B=I/2,          supp(B)=I,          Q meet SQS=0.       (5)
```

A subprojection of the rank-one `Q` is either zero or `Q`, and `Q` is not
reduced by `S`; hence zero is the only reducing subprojection.  This proves
that Reynolds support containment does not imply an invariant source
subcorner, even at zero defect and in dimension two.

Finally, averaging over a fixed finite group, taking support projections,
and applying finite tracial inequalities all extend to the canonical finite
von Neumann algebra.  Applying any proposed dimension-free tracial
native-authentication estimate to `(PGR2)` there would give the forbidden
fixed regular occurrence.  Hence the result may feed a genuinely matricial
mixed-incidence step, but cannot itself bypass the regular firewall.
