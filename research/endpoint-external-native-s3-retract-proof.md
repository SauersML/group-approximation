---
rg: 2
id: endpoint-external-native-s3-retract-proof
kind: route
title: Cut by the complement of the endpoint cylinder and retain the constant two-root S3
target: endpoint-external-subgroup-has-native-s3-retract
requires:
  - endpoint-external-order-four-is-conditional-s3-breaker
  - native-weyl-return-gauges-have-s3-model
---

Put

```text
e=s_00t_00,       f=s_000t_000,
c=s_000t_00,      d=s_00t_000,       r=1-e.            (1)
```

The Leavitt prefix relations give

```text
f<=e,       ec=ce=c,       ed=de=d.                    (2)
```

Hence `r` annihilates `e,f,c,d` on both sides.  On coordinates `(2,8)`,
the endpoint partial Whitehead has the block

```text
P = [[1-f,c],[d,1-e]],                                 (3)
```

and is the identity on the other coordinates.  Multiplying `(3)` on either
side by the scalar projection `rI` therefore gives

```text
(rI)P=P(rI)=rI.                                        (4)
```

The roots `n=x_78(1)` and `m=x_87(1)` have only coefficients zero and one,
so they commute with `rI`; their corner restrictions are

```text
n_r=rI+rE_78,              m_r=rI+rE_87.              (5)
```

The corner is nonzero: `q=s_1t_1` is orthogonal to `e`, and `rq=q!=0`.
Thus `r` is a nonzero identity in `rRr`.  Direct two-by-two multiplication
over the prime subring `{0,r}` gives

```text
n_r^2=m_r^2=(n_rm_r)^3=rI                              (6)
```

and six distinct products.  Therefore `<n_r,m_r>` is `GL_2(F_2)=S_3`.

Because `rI` commutes with every generator of `G=<P,n,m>`, the map

```text
pi:G -> GL(rR^9),             g |-> (rI)g(rI)          (7)
```

is a homomorphism, with identity `rI` in the target corner.  Equations
`(4)--(6)` show that its image is `S_3`, that `pi(P)=1`, and that its
restriction to `N=<n,m>` is injective.  Identifying `pi(N)` with `N` yields
the split retraction in `(ESR2)`.

For calibration only, the MSI artifact enumerates all freely reduced words
through length fourteen using faithful sparse Leavitt normal forms.  It
finds the first odd-`P` cyclic class at length thirteen, represented by

```text
P n P n m P m n P n m P m.                            (8)
```

The artifact verifies `(8)=1` exactly.  Deleting `P` leaves
`n n m m n n m m`, whose involutive free reduction is empty.  This bounded
enumeration is not used to infer the all-word statement; that statement is
the algebraic corner retraction `(7)`.

