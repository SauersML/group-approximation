---
rg: 2
id: split-native-separator-over-finite-faces-and-positivize
kind: route
title: Split the native separator over the finite faces and positivize each component
target: ideal-block-infeasibility-has-positive-reservoir-witness
requires:
  - finite-packet-triangle-repair-is-ideal-block-choi-feasibility
  - three-face-quotient-separators-are-not-one-face-local
  - tree-face-separator-signedness-is-removable-modulo-the-unit
---

First observe that

```text
(T+V) intersect UCP_z(E,J)
  =(T+V_0) intersect UCP_z(E,J).                            (1)
```

Indeed, if `T+v` is relative-unital, then evaluation at the unit gives
`z+v(1)=z`, hence `v in V_0`.  The reverse inclusion is immediate.

Work in the finite-dimensional real vector space `X=L_sa(E,J)`.  The affine
space `T+V_0` is closed and `UCP_z(E,J)` is compact convex.  If `(1)` is
empty, strong separation gives a real functional `F` with

```text
F(T)>sup_(theta in UCP_z(E,J)) F(theta),
F(V_0)=0.                                                   (2)
```

The second assertion follows because a functional bounded on the whole
affine space `T+V_0` must vanish on its direction space.  Rescale so
`||F||=1`, where maps carry the operator norm.

Use the fixed bounded face splitting `(SQS7)`:

```text
R_ij:E->B_ij,             sum_(ij) inclusion_ij R_ij=id_E. (3)
```

For a self-adjoint map `alpha:B_ij->J`, define

```text
F_ij(alpha)=F(alpha o R_ij).                               (4)
```

Then

```text
F(psi)=sum_(ij) F_ij(psi|_(B_ij)),
||F_ij||<=||R_ij|| ||F||.                                  (5)
```

Each `B_ij` is a fixed finite-dimensional C-star algebra.  Apply the positive
Choi conversion from
`tree-face-separator-signedness-is-removable-modulo-the-unit` to `F_ij`.  The
underlying conversion is valid for any finite algebra, not only a tree face.
It gives a functional `Omega_ij` such that

```text
Omega_ij(alpha)>=0                    for every cp alpha,
Omega_ij(alpha)=F_ij(alpha)           if alpha(1)=0,
||Omega_ij||<=C_ij ||F_ij||,                               (6)
```

where `C_ij` depends only on `B_ij`, never on the target algebra `J`.

Define on maps `E->J`

```text
Omega(psi)=sum_(ij) Omega_ij(psi|_(B_ij)).                 (7)
```

If `psi` is cp, every face restriction is cp, so `(6)` makes `(7)`
nonnegative.  If `psi(1)=0`, all three restrictions vanish at their common
unit and `(5)`--`(7)` give

```text
Omega(psi)=F(psi).                                         (8)
```

In particular `(8)` and `(2)` show that `Omega(V_0)=0`.  Since both `T` and
every map in `UCP_z(E,J)` have the same value `z` at the unit, their
differences are unit-zero.  Equation `(8)` therefore preserves every
difference

```text
Omega(T)-Omega(theta)=F(T)-F(theta),                       (9)
```

so the strict separation gap is unchanged.

Restriction to a unital face is contractive.  Equations `(5)`--`(7)` give

```text
||Omega||<=sum_(ij) C_ij ||R_ij|| ||F||
           =:C_Delta ||F||.                               (10)
```

The constant is fixed before `J` or a representation packet is chosen.
Finally, finite-dimensional operator-system duality identifies functionals
nonnegative on the cp-map cone with positive Choi functionals.  Hence
`Omega` is a positive witness in the same native target block and
`(9)`--`(10)` prove the dimension-uniform claim.
