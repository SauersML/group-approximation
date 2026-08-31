---
rg: 2
id: regular-hecke-kraus-support-has-exact-order-dual
kind: claim
title: The regular Hecke--Kraus support has an exact commutant-order dual
distinct_from:
  regular-core-window-is-a-hecke-kraus-hull: that parametrizes the relative matrix range and bounds its support by one scalar top eigenvalue; this computes the support exactly through a noncentral right-multiplication majorant.
  relative-induced-selector-gap-has-bounded-dual-witness: that gives the general Choi support SDP for an arbitrary prescribed core representation; this eliminates the Choi variables in the regular-core case and exposes the finite commutant order.
  hecke-top-spectrum-coverage-controls-window: that characterizes exact membership and an upper bound from near-top frames; this gives exact lower-bound certificates and the full distance dual.
---

Let `G` be finite, `B<G`, `lambda=lambda_G` on `H=ell^2(G)`, and

```text
D=(lambda(B))',       X_0=lambda(x)=X_0*=X_0^(-1)
```

for an involution `x in G`. Let `tau` be normalized trace, let `E_D` be
the trace-preserving expectation onto `D`, and let `K` be the regular
relative Hecke--Kraus hull

```text
K={sum_j A_j* X_0 A_j : A_j in D, sum_j A_j*A_j=1}.    (HOD1)
```

For `Y=Y* in B(H)` define the selfadjoint operator on `L^2(D,tau)`

```text
T_Y(A)=E_D(X_0 A Y),
```

and, for `Z=Z* in D`, define right multiplication

```text
R_Z(A)=A Z.
```

Then the support function of `K` has the exact order dual

```text
h(Y):=sup_(C in K) tau(YC)
     =min {tau(Z): Z=Z* in D and R_Z >= T_Y}.           (HOD2)
```

The inequality in (HOD2) is positivity of an operator on the finite
Hilbert space `L^2(D,tau)`. In particular, any feasible pair `(Y,Z)`
gives the certified selector lower bound

```text
dist_2(X,K) >= tau(YX)-tau(Z)                           (HOD3)
```

whenever `X=X*` and `||Y||_2<=1`.

In fact the complete distance is the single finite conic program

```text
dist_2(X,K)
 =max {tau(YX)-tau(Z):
       Y=Y*, Z=Z*, ||Y||_2<=1, R_Z>=T_Y}.              (HOD4)
```

Thus (HOD3) is not a relaxation: optimizing all commutant-order
certificates recovers the exact relative selector gap. The Hilbert--Schmidt
ball is semidefinite representable, so (HOD4) is an explicit finite SDP.

Taking

```text
Z=lambda_max(T_Y) 1
```

is always feasible and recovers the earlier numerical-radius estimate.
Allowing a noncentral `Z` can give a strictly smaller trace majorant and
hence a sharper obstruction. Conversely, primal Kraus frames give exact
upper bounds. The remaining Iwahori question is now concrete: prove that
the value of (HOD4) tends to zero for every authenticated regular
microstate, or exhibit feasible moving pairs with a positive limiting
objective. No available LLP, MF, or Fejer--Riesz theorem controls these
noncentral commutant-order majorants uniformly in the moving level.
The nonhyperlinear-group root remains open.

DERIVATION
regular-hecke-kraus-order-dual-proof
