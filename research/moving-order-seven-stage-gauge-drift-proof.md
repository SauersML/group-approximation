---
rg: 2
id: moving-order-seven-stage-gauge-drift-proof
kind: route
title: Twist the six intermediate charts of an exact seven-cycle
target: moving-order-seven-stage-gauges-have-coboundary-drift
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Let `sigma` be any finite-dimensional unitary representation of the finite
packet `Gamma=GL_3(F_2)` and write

```text
M=sigma(t),                    t=JBA,                    (1)
```

so `M^7=1`.  Let `lambda` be the left regular representation of `Gamma` and
let `K` be a two-dimensional multiplicity space carrying a nontrivial
self-adjoint involution `V`.  On

```text
H=H_sigma tensor l^2(Gamma) tensor K
```

use the exact packet representation

```text
pi(g)=sigma(g) tensor lambda(g) tensor 1_K.             (2)
```

Fix `r in Gamma`.  The seven vectors

```text
delta_r,delta_(tr),...,delta_(t^6r)
```

are distinct because `t` has order seven.  Let `E_k` project onto

```text
H_sigma tensor C delta_(t^k r) tensor K.               (3)
```

Then `E_7=E_0` and `T=pi(t)` maps `E_kH` unitarily onto `E_(k+1)H`.
Every term `(1-E_(k+1))TE_k` is exactly zero.

Choose the standard stage charts

```text
phi_k(x tensor z)=x tensor delta_(t^k r) tensor z.      (4)
```

They identify every transition with `M tensor 1`.  Now retain the initial
chart and replace the intermediate charts by

```text
psi_k=phi_k(1 tensor U_k),       U_0=U_7=1.             (5)
```

In these charts the `k`-th transition is

```text
psi_(k+1)^* T psi_k
  =M tensor (U_(k+1)^* U_k).                            (6)
```

Given commuting self-adjoint involutions `D_0,...,D_6` with product one,
define recursively

```text
U_(k+1)=U_k D_k.                                        (7)
```

Then `U_7=1`, and `(6)` is `M tensor D_k`.  Taking
`D_0=D_1=V` and all remaining `D_k=1` proves the claimed drift while
leaving `psi_0=phi_0`, so any Pauli or selector convention fixed solely on
the initial source is unchanged.

More generally, arbitrary stage changes replace transition gauges by

```text
D_k -> U_(k+1)^* D_k U_k,                              (8)
```

the usual coboundary action.  Only the cyclic product, up to conjugacy at
the initial stage, survives.  Equation `T^7=1` constrains that product; it
cannot distinguish the two equal nontrivial factors in `(MGC4)` from seven
trivial factors.  Therefore equality of the seven gauges must come from
extra cross-stage intertwiners with fixed coefficient typing, not from the
order-seven telescope or moving cuts themselves.

There is also a transported-conjugacy version.  On `K_0=C^7`, let
`Ue_j=e_(j+1)` (indices modulo seven) and let

```text
De_j=-e_j for j=0,1,       De_j=e_j otherwise.         (9)
```

For `D_k=U^kDU^(-k)`, all seven gauges are conjugate copies of the one
named nontrivial involution `D`.  They are diagonal, and on each coordinate
exactly two of them have sign `-1`; therefore

```text
D_6D_5...D_0=1.                                      (10)
```

Using `M tensor D_k` for the transition from the `k`-th orbit summand to
the next gives zero boundary, the fixed label matrix `M`, transported
conjugate stage gauges, and exact seventh-power return, while `D!=1`.
Consequently even conjugacy synchronization gives only the norm product
`(10)`.  Turning it into `D^7` requires commutation with the reservoir
transport or an equivalent fixed-frame coefficient lock.

Here is the marked-source strengthening.  Let `H_7` be the seven-pair
extraspecial group from
`middle-index-order-seven-orbit-cut-is-native-scale-neutral` and let its
Schrodinger representation `rho` act on `S=ell^2(F_2^7)`, with
`rho(z)=-I`.  Every binary linear change of the seven coordinates acts on
`S` by

```text
(U_L f)(x)=f(L^(-1)x),                                 (11)
```

and normalizes `rho(H_7)`.  Take `K=GL_7(F_2)` and its left regular
representation `lambda_K`.  Then

```text
Pi(h,L)=rho(h)U_L tensor lambda_K(L)                   (12)
```

is an exact finite-dimensional representation of `H_7 semidirect K`.
It contains every actual binary actor displayed in the seven-pair packet,
including `L_0` and the two matrices `T_1,T_2` from
`el20-order-seven-zero-cut-block-proof`.

Let `lambda_0` be the signed character of `L_0` used there and form its
Reynolds projection `Q` in `(10)`.  Since
`lambda_K|_(L_0)` is `[K:L_0]` copies of the regular representation and a
regular representation absorbs tensoring by any finite representation,

```text
rank(Q)=dim(S)[K:L_0]>0.                               (13)
```

Meanwhile `z` acts as `-I`, so this is a positive marked signed source.
For either actual head, put

```text
E_(i,k)=Pi(T_i)^k Q Pi(T_i)^(-k).                      (14)
```

The literal order-seven relation gives `E_(i,7)=Q`, and every transition
boundary is zero.  Finally amplify `(10)` by `1_(C^2)`.  The nontrivial
involution `V` on that spectator commutes with every named Heisenberg and
actor label, so the chart twist `(5)--(7)` preserves every separate stage
typing while producing `(V,V,1,...,1)`.

This finite semidirect model realizes the actual block-level EL20 relations
used by the present order-seven and Heisenberg nodes, but it is not a
representation of all of `EL_20(L_(F_2)(1,2))`: the omitted Leavitt
coefficient relations are exactly where a genuine cross-stage lock would
have to enter.
