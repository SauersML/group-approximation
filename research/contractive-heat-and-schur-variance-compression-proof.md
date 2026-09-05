---
rg: 2
id: contractive-heat-and-schur-variance-compression-proof
kind: route
title: Improve the compressed inclusion by heat and bound its irreducible Schur variance
target: kazhdan-irreducible-compressions-have-quadratic-defect
requires:
  - kazhdan-approximate-coefficients-have-curved-hodge-control
artifacts:
  - research/artifacts/general-irreducible-compression-quadratic-defect-2026-09-05.md
---

Let d=N-k and W:C^d->C^N include the retained space. For
B_s=W*rho(s)W, the positive contraction I-B_s*B_s has rank at most k.
Its singular values c_i therefore give any unitary polar completion
the edge bound `||rho(s)W-WU_s||HS^2=2sum_i(1-c_i)<=2k`.
Fixed-word telescoping proves `delta^2<=2ell^2 k/d`, where ell is
the maximal relator length.

Let mu,C_H,delta_H be the curved Hodge constants, h=|S|, and
K0=|R|+4C_H. Choose

```text
theta_0=min(1/2,mu/(8h),kappa^2/4),
B0=2h theta_0+K0/mu.
```

The coefficient heat flow A_t from W has initial normalized squared
mass one, initial energy at most 2h k/d, and operator norm at most
one throughout. At t=log(1/delta)/mu, the required heat theorem gives

```text
E(t)<=B0 delta^2,
N(t)>=1-2h theta_0/mu-(2K0/mu^2)delta^2 log(1/delta).
```

For small enough positive delta, N(t)>=1/2. If delta=0 and k>0,
U is exact of dimension d<N, so Hom(U,rho) has no invariant vector.
Property (T) on W would give kappa^2 d<=2k, contrary to the chosen
theta_0. Thus that exceptional case cannot occur.

Put A=A_t and Q=AA*. Contractivity implies

```text
||rho(s)Qrho(s)*-Q||HS<=2||rho(s)A-AU_s||HS.
```

The invariant matrices in Ad(rho) are scalar. Property (T) therefore
gives

```text
||Q-(TrQ/N)I_N||HS^2 <=(4B0/kappa^2)delta^2 d.
```

Since rank Q<=d and TrQ>=d/2, Cauchy--Schwarz gives the opposite bound

```text
Tr Q^2-(TrQ)^2/N >=(TrQ)^2(1/d-1/N) >=d k/(4N).
```

Hence `k/d<=16(1+theta_0)B0 delta^2/kappa^2`. This proves the
lower defect bound for small delta. Above the fixed small-defect
threshold delta_1, use `k/d<=theta_0<=theta_0 delta^2/delta_1^2`.
Enlarging the constant proves `(KIC1)` throughout the stated ratio
range. No finite-image property or H2 hypothesis entered this argument.

Finally, in the small-positive-defect regime,
`E(t)<=B0 delta^2` and `N(t)>=1/2` give the heat vector
Rayleigh quotient at most `(2B0/h)delta^2` for the coefficient
connection Laplacian L0/h. This proves `(KIC2)` and its stated
spectral consequence without introducing any finite quotient host.
