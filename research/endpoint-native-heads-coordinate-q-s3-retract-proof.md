---
rg: 2
id: endpoint-native-heads-coordinate-q-s3-retract-proof
kind: route
title: Keep q only on the two constant-root coordinates
target: endpoint-native-heads-retain-coordinate-q-s3-retract
requires:
  - endpoint-b2-enlargement-has-native-s3-retract
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Let `e_i` be the standard coordinate idempotents and write

```text
E=q(E_77+E_88).
```

For a matrix root `X=x_ij(a)=I+aE_ij`, direct multiplication gives

```text
E(X-I)=q_i a E_ij,             (X-I)E=a q_j E_ij,    (1)
```

where `q_7=q_8=q` and every other `q_k` is zero.  Hence `X` commutes with
`E` and restricts to the identity on its corner exactly when

```text
q_i a=a q_j=0.                                      (2)
```

The Leavitt prefix relations give

```text
q b_2=(s_1t_1)(s_00t_1)=0,
a_1q=(s_1t_0)(s_1t_1)=0,
a_2q=(s_1t_00)(s_1t_1)=0.                          (3)
```

Now `B_2` has `(i,j)=(8,4)`, so `(3)` and the absence of coordinate `4`
from `E` prove `(2)`.  The roots `A_1,A_2` have positions `(4,7)` and
`(5,8)`, so the other two equations in `(3)` prove `(2)` for them.
The root `B_3` has position `(9,5)` and is disjoint from coordinates
`7,8`, so `(2)` is automatic.

Every nonidentity coefficient of `P,J_1,J_2` is two-sidedly supported
under `p=s_0t_0`.  Since `pq=qp=0`, multiplying any such deviation from
either side by `E` gives zero.  Thus the three partial Whiteheads commute
with `E` and restrict to its identity.

The constant roots `n=x_78(1)` and `m=x_87(1)` commute with `E` because
the same idempotent `q` occurs on both coordinates.  Their restrictions are

```text
n_E=E+qE_78,                    m_E=E+qE_87.          (4)
```

The unital prime subring `{0,q}` of the nonzero corner `qRq` is `F_2`.
On coordinates `7,8`, `(4)` is therefore the standard pair of opposite
transvections generating `GL_2(F_2)`, and the corner map is injective on
`N=<n,m>`.

Because `E` commutes with every generator, corner restriction is a group
homomorphism.  It kills all seven nonconstant generators and identifies
its image with `N`, proving the split retraction.  Products of killed
generators, including the two displayed native heads, are killed as well.

Finally `(1)` gives the exact scope boundary `(NHR2)`.  In particular
`x_84(1)` fails it on the left because `q*1=q!=0`, whereas `A_2` satisfies
it by `(3)` even though `a_2` is not in the left ideal `pR`.
