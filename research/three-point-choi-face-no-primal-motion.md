---
rg: 2
id: three-point-choi-face-no-primal-motion
kind: route
title: Separate one vertex from the opposite Choi face by the signed closing coordinate
target: supporting-choi-component-does-not-force-primal-motion
requires: []
---

Let `E=C^3` with minimal projections `e_1,e_2,e_3`, and identify
`UCP(E,C)` with its state simplex

```text
Delta_2={(p_1,p_2,p_3):p_i>=0, p_1+p_2+p_3=1}.
```

Take

```text
K={(p_1,p_2,0):p_1+p_2=1},
psi=(0,0,1),
e=(1,0,0).                                                 (1)
```

Thus `K` is the closing-coordinate-zero Choi face and contains the
distinguished scalar comparison `e`.  Put

```text
h=2e_3-1_E=(-1,-1,1),
ell(T)=T(h).                                                (2)
```

Since `||h||=1`, evaluation at `h` has norm one on the Banach space of maps
`E->C`.  Every `phi in K` satisfies `phi(h)=-1`, whereas `psi(h)=1`.
Consequently

```text
ell(psi)-sup_(phi in K)ell(phi)=2.                         (3)
```

The state-norm distance from `psi` to every `phi in K` is also `2`, because
their support projections are orthogonal; equivalently, `(2)` is a norming
functional for every difference `psi-phi`.  Hence every point of `K` is a
closest point and `ell` belongs to the exact normal cone there.  This is the
strongest closest-point/complementary-slackness situation one could ask for.

On unital differences the unit term in `(2)` vanishes, so

```text
ell(psi-e)=2(psi-e)(e_3)=2.                                (4)
```

The entire centered separator value is therefore the named closing
coordinate.  Nevertheless

```text
phi(e_3)=0=e(e_3)              for every phi in K.         (5)
```

Thus every closest feasible comparison has zero primal closing movement from
`e`, proving `(SCP1)--(SCP2)` and refuting the generic inference `(SCP3)`.
