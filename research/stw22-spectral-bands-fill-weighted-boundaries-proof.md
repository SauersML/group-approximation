---
rg: 2
id: stw22-spectral-bands-fill-weighted-boundaries-proof
kind: route
title: Extend spectral bands recursively and take their uniform weighted sum
target: stw22-low-spectrum-weighted-boundary-filling
requires:
  - stw22-hyperfinite-stiefel-all-sphere-fillings
artifacts:
  - research/artifacts/stw22-low-spectrum-boundary-extension-audit-2026-08-30.md
---

Write `p=supp(b)`.  The case `b=0` is immediate.  For `n>=0` put

```text
I_n=(eta 2^(-(n+1)),eta 2^(-n)],
r_n=1_(I_n)(b).
```

Discard the zero `r_n`.  The projections `r_n` are orthogonal and sum
strongly to `p`.  Although the polar frame of `x(z)` need not be
continuous on all of `p`, the band frame

```text
xi_n(z)=x(z)b^(-1/2)r_n                              (SB1)
```

is `2`-norm continuous because `b^(-1/2)r_n` is bounded.  Moreover

```text
xi_n(z)^*xi_n(z)=r_n,       xi_n(z)xi_n(z)^*<=f(z),
```

and the final projections of different band frames are orthogonal.

## The relative one-band extension

We use the following consequence of two established selection results.
If `g:B^(m+1)->R` is a `2`-norm-continuous projection field of constant trace,
`r` is a projection with `tau(r)<=tau(g(y))`, and

```text
xi:S^m->{v:v^*v=r, vv^*<=g(z)}
```

is continuous, then `xi` extends over `B^(m+1)` with the same equations.

Indeed, the continuous projection-equivalence theorem of Farah--Vaccaro,
Theorem 1.1 with the McDuff extension recorded immediately after its proof,
applies over the finite-dimensional compact space `B^(m+1)` to `R`.  It gives a
continuous unitary field `u(y)` such that, for `g_0=g(y_*)`,

```text
u(y)g_0u(y)^*=g(y).
```

Thus `zeta(z)=u(z)^*xi(z)` is an `m`-sphere in the fixed strong Stiefel space
`V(r,g_0)`.

The claim `stw22-hyperfinite-stiefel-all-sphere-fillings` says that this
fixed Stiefel space is `m`-connected.  Fill `zeta` over `B^(m+1)` and
multiply by `u(y)`.  This proves the one-band extension with the exact
prescribed boundary, in every finite degree, without any quotient
cross-section.

## Orthogonal recursion

Assume continuous extensions `V_0,...,V_(n-1)` have been constructed with
boundary values `xi_0,...,xi_(n-1)` and mutually orthogonal final
projections.  Put

```text
g_n(y)=f(y)-sum_(k<n)V_k(y)V_k(y)^*.
```

This is a `2`-norm-continuous projection field of constant trace.  On the
boundary, `xi_n(z)` takes values in `g_n(z)`, and

```text
tau(g_n(y))
 =tau(f(y))-sum_(k<n)tau(r_k)
 >=tau(p)-sum_(k<n)tau(r_k)
 >=tau(r_n).                                           (SB2)
```

The one-band extension therefore gives `V_n:B^(m+1)->R` with

```text
V_n^*V_n=r_n,       V_nV_n^*<=g_n,       V_n|_(S^m)=xi_n.
```

This completes the recursion.

## The weighted diagonal limit

Define

```text
X_N(y)=sum_(n=0)^N V_n(y)b^(1/2)r_n.                   (SB3)
```

Orthogonality gives, uniformly in `y`,

```text
||X_M(y)-X_N(y)||_2^2
 =sum_(N<n<=M)tau(br_n).                               (SB4)
```

The right side tends to zero because `sum r_n=p`.  Hence `(X_N)` converges
uniformly in `2`-norm to a continuous `X:B^(m+1)->L^2(R)`.  Also
`||X_N||<=sqrt(eta)`; a uniformly operator-bounded `L^2` limit belongs to
`R`.  Passing to the limit in `L^1` in `(SB3)` gives

```text
X(y)^*X(y)=sum_n br_n=b.
```

Since `f(y)X_N(y)=X_N(y)`, also `f(y)X(y)=X(y)`.  On the boundary,

```text
X_N(z)=x(z)sum_(n<=N)r_n,       z in S^m,
```

and `(SB4)` shows uniform convergence to `x(z)`.  Thus `(LSW)` holds with
the exact prescribed boundary.  Finally the triangle inequality gives

```text
||X(y)-x_0||_2<=||X(y)||_2+||x_0||_2
 =2sqrt(tau(b))<=2sqrt(eta s),
```

which is `(LSB)`.

The projection-equivalence input is I. Farah and A. Vaccaro,
[*Continuous Selection of Unitaries in II_1 Factors*](https://arxiv.org/abs/2501.01272),
Proc. Amer. Math. Soc. 154 (2026), Theorem 1.1 and the McDuff extension
immediately following its proof.
