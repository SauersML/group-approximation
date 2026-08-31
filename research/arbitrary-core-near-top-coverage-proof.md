---
rg: 2
id: arbitrary-core-near-top-coverage-proof
kind: route
title: Fill the missing carrier through the canonical induced core copy
target: arbitrary-core-near-top-coverage-controls-relative-corner
requires:
  - relative-induced-selector-has-intertwiner-order-dual
  - almost-full-hecke-frame-gives-flexible-corner
---

Let

```text
J:H_beta->H_rho
```

be the canonical identity-coset inclusion in `rho=Ind_B^G(beta)`. It is
a `B`-intertwining isometry, hence `J in E_beta` and `J*J=1`.

From (ACN2), `P in D_beta`. Functional calculus therefore gives
`(1-P)^(1/2) in D_beta`, and the right-module property of `E_beta`
shows that

```text
V_0=J(1-P)^(1/2) in E_beta,
V_0*V_0=1-P.                                           (ACP1)
```

Thus the enlarged family is unital:

```text
sum_(j>=0) V_j*V_j=1.                                  (ACP2)
```

Put `X_0=rho(x)` and

```text
E_j=X_0V_j-V_jX.
```

Since left multiplication by `X_0` and right multiplication by `X` are
Hilbert--Schmidt isometries, while `P_E` is an orthogonal projection,
`T_X` is a selfadjoint contraction. For the near-top columns, spectral
calculus gives

```text
sum_(j>=1) ||E_j||_(2,d)^2
 =2 sum_(j>=1) <V_j,(1-T_X)V_j>
 <=2 epsilon sum_(j>=1)||V_j||_(2,d)^2
 =2 epsilon tr_d(P)
 <=2 epsilon.                                          (ACP3)
```

For the filler, unitarity and (ACP1) give

```text
||E_0||_(2,d)<=2||V_0||_(2,d),
||V_0||_(2,d)^2=tr_d(1-P)<=delta.                      (ACP4)
```

The frame (ACP2) defines a core-exact relative ucp map with marked
coefficient

```text
C=sum_(j>=0) V_j*X_0V_j.
```

Moreover

```text
C-X=sum_(j>=0) V_j*E_j.                                (ACP5)
```

The row operator `(V_0*,V_1*,...)` is a coisometry by (ACP2), so its
product with the error column has normalized Hilbert--Schmidt norm at
most the column norm. Equations (ACP3)--(ACP5) yield

```text
||C-X||_(2,d)<=sqrt(2 epsilon+4 delta),                (ACP6)
```

proving (ACN3).

## Dualize the optimal coverage

Let `L_epsilon=Q_epsilon E_beta` and define

```text
Psi_epsilon:B(L_epsilon)->D_beta,
Psi_epsilon(|V><W|)=W*V.                               (ACP7)
```

For `S>=0` with decomposition `S=sum_j|V_j><V_j|`,

```text
Psi_epsilon(S)=sum_jV_j*V_j,
Tr(S)=sum_j||V_j||_(2,d)^2=tr_d(Psi_epsilon(S)).       (ACP8)
```

Hence (ACN4) is the attained finite SDP

```text
c_(epsilon,beta)
 =max {Tr(S): S>=0, Psi_epsilon(S)<=1}.                (ACP9)
```

The feasible set is compact because every feasible `S` has trace at
most one.

For `Z=Z* in D_beta`, the adjoint identity is

```text
tr_d(Z Psi_epsilon(S))
 =Tr(Q_epsilon R_Z Q_epsilon S).                       (ACP10)
```

Therefore the dual of (ACP9) is exactly (ACN5). Strong duality and
attainment hold: `Z=c1` with `c>1` is strictly dual feasible, and a
sufficiently small positive multiple of the identity on `L_epsilon` is
strictly primal feasible. The zero-space case is immediate.

Choose a primal optimizer in (ACP9). It supplies (ACN2) with

```text
delta=1-c_(epsilon,beta).
```

Equation (ACN3) now gives (ACN6). If `Delta>=eta` and
`epsilon<=eta^2/4`, then squaring (ACN6) yields

```text
1-c_(epsilon,beta)
 >=(eta^2-2 epsilon)/4
 >=eta^2/8.                                            (ACP11)
```

An attained optimizer `Z` in (ACN5) consequently obeys (ACN7). Finally,
for `V in L_epsilon`, its compressed order inequality reads

```text
<V,R_ZV>=tr_d(V*VZ)=tr_d(ZV*V)>=||V||_(2,d)^2,         (ACP12)
```

which is (ACN8).
