---
rg: 2
id: relative-induced-intertwiner-order-dual-proof
kind: route
title: Dualize Gram frames in the induced intertwiner module
target: relative-induced-selector-has-intertwiner-order-dual
requires:
  - every-relative-ucp-window-lives-in-one-induced-representation
  - relative-induced-selector-gap-has-bounded-dual-witness
---

First note that `E_beta` is a right module over `D_beta`. Indeed, if
`V` intertwines `beta` with `rho|_B` and `Z` commutes with `beta(B)`,
then `VZ` is again an intertwiner. Also, for `V,W in E_beta`,

```text
W*V in D_beta.                                         (IOP1)
```

This follows by moving `beta(b)` through `W* rho(b) V`.

For selfadjoint `Y`, orthogonal projection and cyclicity of normalized
trace give

```text
<W,T_Y V>
 =tr_d(W* X_0 VY)
 =tr_d(Y W* X_0 V)
 =<T_Y W,V>.                                           (IOP2)
```

Thus `T_Y` is selfadjoint. The right-module observation shows that
`R_Z` preserves `E_beta`, and it is selfadjoint when `Z=Z*`.

## Convexify the induced isometries exactly

Consider arbitrary finite families `V_j in E_beta` satisfying

```text
sum_j V_j*V_j=1.                                       (IOP3)
```

They define the ucp map

```text
Theta(a)=sum_j V_j* rho(a)V_j.                         (IOP4)
```

For `b in B`, intertwining and (IOP3) give

```text
Theta(u_b)=sum_j V_j*V_j beta(b)=beta(b).              (IOP5)
```

So every such family gives a point of `K`. Conversely, the universal
relative induced-host theorem represents every core-exact ucp map by a
single `B`-intertwining isometry into `rho`, which is the one-column
case of (IOP3). Hence

```text
K={sum_j V_j*X_0V_j:
   V_j in E_beta, sum_j V_j*V_j=1}.                    (IOP6)
```

The same theorem recompresses every finite family back into the one
induced host, so allowing arbitrary column count is exact.

## The Gram primal and its dual

On the finite Hilbert space `E_beta`, define

```text
Psi:B(E_beta)->D_beta,
Psi(|V><W|)=W*V.                                       (IOP7)
```

If `S>=0`, choose a decomposition

```text
S=sum_j |V_j><V_j|.
```

Then

```text
Psi(S)=sum_j V_j*V_j,
Tr_(E_beta)(S)=sum_j ||V_j||_2^2=tr_d(Psi(S)),
Tr_(E_beta)(T_Y S)
 =sum_j tr_d(Y V_j*X_0V_j).                            (IOP8)
```

By (IOP6), the exact support problem is

```text
h_beta(Y)=max {Tr(T_Y S): S>=0, Psi(S)=1}.             (IOP9)
```

The feasible set is compact because every feasible `S` has trace one.

Pair `D_beta` with itself using `tr_d`. For `Z=Z* in D_beta`,
a rank-one calculation gives

```text
tr_d(Z Psi(S))=Tr_(E_beta)(R_Z S).                     (IOP10)
```

Thus `Psi*(Z)=R_Z`, and the SDP dual of (IOP9) is

```text
min {tr_d(Z): Z=Z* in D_beta, R_Z-T_Y>=0}.             (IOP11)
```

The primal is feasible, using any universal induced isometry for one
core-exact ucp map. More directly, the canonical identity-coset inclusion
is such an isometry. The dual is strictly feasible with `Z=c1` for
`c>||T_Y||`. Finite-dimensional SDP strong duality gives equality and
attainment, proving (IOD3).

Finally, `K` is compact and convex as the image under evaluation at
`u_x` of the compact convex set of core-exact ucp maps. It lies in the
selfadjoint matrices because `x` is an involution. The real Hilbert-space
support formula therefore gives

```text
Delta_(G,B,beta)(X)
 =max_(Y=Y*, ||Y||_(2,d)<=1)
    (tr_d(YX)-h_beta(Y)).                              (IOP12)
```

Substitution of (IOP11), with the attained minimizing `Z` for each `Y`,
is exactly (IOD4). In real coordinates the order constraint is an LMI,
and the Hilbert--Schmidt ball has the standard arrow-matrix LMI, so the
whole variational formula is a finite SDP.
