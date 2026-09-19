---
rg: 2
id: regular-hecke-kraus-order-dual-proof
kind: route
title: Dualize the Kraus frame constraint inside the finite commutant
target: regular-hecke-kraus-support-has-exact-order-dual
requires:
  - regular-core-window-is-a-hecke-kraus-hull
  - relative-induced-selector-gap-has-bounded-dual-witness
---

All Hilbert spaces below are finite dimensional. Give `D` the inner
product

```text
<A,C>=tau(A* C).
```

For selfadjoint `Y`, the operator `T_Y` is selfadjoint. Indeed, for
`A,C in D`, trace preservation of `E_D` and cyclicity give

```text
<C,T_Y A>
 =tau(C* X_0 A Y)
 =tau(Y C* X_0 A)
 =<T_Y C,A>.                                           (HOP1)
```

Right multiplication `R_Z` is likewise selfadjoint when `Z=Z*`.

## Remove the artificial Kraus-number bound

Let `K_infinity` be the right side of (HOD1) with an arbitrary finite
number of Kraus operators. Plainly `K` is contained in `K_infinity`.
Conversely, a finite family `A_j in D` with

```text
sum_j A_j*A_j=1
```

defines the ucp map

```text
Phi(a)=sum_j A_j* lambda(a) A_j.
```

Because every `A_j` commutes with `lambda(B)`, this map is exactly the
regular core representation on `B`. The universal relative induced-host
theorem recompresses its marked coefficient into the fixed host

```text
Ind_B^G(lambda_G|_B) isomorphic to [G:B] lambda_G.
```

Hence the same coefficient has a Kraus expression with at most `[G:B]`
columns. Therefore

```text
K_infinity=K.                                          (HOP2)
```

This step is what makes the following convex semidefinite variable exact,
rather than a rank relaxation.

## A Gram-matrix primal

Let `L=L^2(D,tau)`. Define the linear map

```text
Psi:B(L) -> D
Psi(|A><C|)=C* A,                                      (HOP3)
```

first on rank-one operators and then by linearity. Every positive
`S in B(L)` has a decomposition

```text
S=sum_j |A_j><A_j|.
```

Equations (HOP2)--(HOP3) show

```text
Psi(S)=1       iff       sum_j A_j*A_j=1.              (HOP4)
```

Moreover

```text
Tr_L(T_Y S)
 =sum_j <A_j,T_Y A_j>
 =sum_j tau(Y A_j* X_0 A_j).                           (HOP5)
```

Thus the exact support problem is the finite SDP

```text
h(Y)=max {Tr_L(T_Y S): S>=0, Psi(S)=1}.                (HOP6)
```

The feasible set is compact: from (HOP4),

```text
Tr_L(S)=sum_j ||A_j||_2^2=tau(1)=1.
```

## Compute the SDP dual

Use `tau` to pair `D` with itself and the ordinary operator trace to pair
`B(L)` with itself. For `Z=Z* in D` and `S>=0`, a rank-one calculation
gives

```text
tau(Z Psi(S))=Tr_L(R_Z S).                             (HOP7)
```

Therefore the adjoint of `Psi` at `Z` is exactly `R_Z`, and the dual of
(HOP6) is

```text
min {tau(Z): Z=Z* in D, R_Z-T_Y>=0}.                  (HOP8)
```

There is no duality gap. The primal is feasible, for example with
`S=|1><1|`. The dual is strictly feasible: for any real
`c>||T_Y||`, take `Z=c1`, so `R_Z-T_Y=cI-T_Y>0`.
Finite-dimensional SDP strong duality also gives attainment. This proves
(HOD2).

## Insert the Hilbert-space distance dual

Every element of `K` is selfadjoint, and `K` is compact and convex because
it is the image of the compact convex set of core-exact ucp maps. In the
real Hilbert space of selfadjoint matrices, the usual support formula is

```text
dist_2(X,K)
 =max_(Y=Y*, ||Y||_2<=1) (tau(YX)-h(Y)).               (HOP9)
```

Substitute (HOP8). For each fixed `Y`, maximizing `-tau(Z)` over the
feasible majorants chooses the attained minimum in (HOP8). This yields
(HOD4). Equation (HOD3) follows by retaining any one feasible pair.

The earlier scalar numerical-radius bound is the special dual-feasible
choice

```text
Z=lambda_max(T_Y)1.
```

Noncentral majorants can improve it strictly. For example, take
`G=B=C2` and let `x` be its nonidentity element. In the Fourier basis,

```text
D=C direct_sum C,       X_0=diag(1,-1).
```

With `P=diag(1,0)` and `Y=X_0 P=P`, one has `T_Y=R_P`. The optimal
majorant is `Z=P`, with `tau(Z)=1/2`, whereas the scalar choice has
`lambda_max(T_Y)=1`. This verifies that the order-valued dual contains
information genuinely lost by the top-eigenvalue estimate.

Finally, choose real coordinates on the selfadjoint parts of `B(H)` and
`D`. The constraint `R_Z-T_Y>=0` is one linear matrix inequality, and the
Euclidean ball `||Y||_2<=1` has a standard arrow-matrix LMI. Hence (HOD4)
is an explicit finite SDP, as claimed.
