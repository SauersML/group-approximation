---
rg: 2
id: endpoint-constant-root-enlargements-have-marked-finite-quotient
kind: claim
title: Arbitrary constant-root enlargements of the p-supported endpoint packet retain a marked finite quotient
artifacts:
  - research/endpoint-constant-root-finite-quotient-proof.md
distinct_from:
  endpoint-native-heads-retain-coordinate-q-s3-retract: that uses a reducing two-coordinate q-corner and includes the nonconstant A1 and A2 roots; this allows arbitrary constant elementary roots by passing to R/pR, but does not include roots whose coefficients survive nontrivially in that quotient.
  endpoint-b2-enlargement-has-native-s3-retract: that proves an S3 retraction for B2 and three Whiteheads; this identifies the entire finite constant image and shows that even constant roots which destroy the localized q-corner remain harmless finite enlargements.
  endpoint-external-subgroup-has-native-s3-retract: that treats the endpoint and its two opposite constant roots using a complement corner; this handles an arbitrary finite constant-root family at once by a one-sided-support quotient.
---

**ESTABLISHED CONSTANT-ROOT FINITE-IMAGE FENCE.**  Let

```text
p=s_0t_0,                         A=R/pR,
P=What_(8,2;2),                   J_1=What_(7,8;1),
J_2=What_(8,9;2),                 B_2=x_84(s_00t_1),
n=x_78(1),                        m=x_87(1).
```

Let `C` be any finite family of constant elementary roots `x_ij(1)` and
put

```text
G_C=<P,J_1,J_2,B_2,n,m,C>.
```

The action on the nonzero quotient module `A^20` factors through the finite
constant group

```text
bar rho_C:G_C -> <x_78(1),x_87(1),C> <= GL_20(F_2).  (PCR1)
```

It kills `P,J_1,J_2,B_2`, while its restriction to
`<n,m>~=S_3` is faithful.  Therefore `G_C` has a finite quotient retaining
the native mark for every such family `C`.

In particular adjoining the literal constant crossing root `x_84(1)`
does destroy the reducing projection `q(E_77+E_88)`, because
`q*1!=0`, but it is **not** a same-carrier breaker.  For this single inward
crossing the coordinate submodule

```text
A e_7 + A e_8 <= A^20
```

is invariant; `x_84(1)` acts identically there and `n,m` give the standard
`S_3`.  Thus the `x_84(1)` enlargement itself still retracts onto the native
`S_3`.  More generally `(PCR1)` gives an exact marked finite model for any
finite constant-root family.  The same finite-model conclusion holds after
adjoining both constant factors
`x_84(1),x_47(1)` occurring in the external return word

```text
t_1=J_1 x_84(1)x_47(1).
```

Thus the next genuine MF breaker cannot consist solely of more constant
elementary roots attached to the `pR`-supported endpoint packet.  Destroying
even the `S_3` retraction requires an outward crossing as well as the inward
`x_84(1)` (or some equivalent loss of the `7,8` invariant coordinate
submodule).  But such a constant-only enlargement still has the finite
model `(PCR1)`.  An MF breaker must also make a nonconstant coefficient
outside `pR` act nontrivially in the same quotient, or otherwise authenticate
a relation absent from the finite constant image.

No Property `(T)`, Kazhdan input, stability theorem, trace profile,
literature input, or computation is used.

DERIVATION
endpoint-constant-root-finite-quotient-proof
