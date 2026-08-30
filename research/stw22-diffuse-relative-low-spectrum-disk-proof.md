---
rg: 2
id: stw22-diffuse-relative-low-spectrum-disk-proof
kind: route
title: Select every spectral band relatively and sum the weighted extensions
target: stw22-diffuse-relative-low-spectrum-disk-extension
requires:
  - stw22-diffuse-stiefel-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Put `delta_0=tau(e)-tau(p_h)-tau(p_l)>0`. Split the fixed low weight into
spectral bands

```text
I_n=(eta 2^(-(n+1)),eta 2^(-n)],
r_n=1_(I_n)(b),        sum_n r_n=p_l.                    (DR5)
```

Zero bands are discarded. Although the full polar frame of `x` need not
be continuous, each band frame

```text
xi_n(z)=x(z)b^(-1/2)r_n                                (DR6)
```

is `2`-norm continuous, has initial projection `r_n`, and has range
under `f(z)`.

## Relative one-band selection

Suppose bands below `n` have already been extended to continuous partial
isometries `V_0,...,V_(n-1)` with mutually orthogonal ranges, and set

```text
g_n(y)=f(y)-sum_(k<n)V_k(y)V_k(y)^*.                    (DR7)
```

This is a continuous projection field and

```text
tau(g_n(y))-tau(r_n)
 =tau(e)-tau(p_h)-sum_(k<=n)tau(r_k)
 >=delta_0.                                             (DR8)
```

On the disk interior consider the closed nonempty values

```text
Phi_n(y)={v in N:v^*v=r_n, vv^*<=g_n(y)}.               (DR9)
```

On the boundary replace the value by the singleton `{xi_n(y)}`. We verify
Michael's degree-one hypotheses.

* **Lower semicontinuity.** If `v_0v_0^*<=g_n(y_0)` and `y->y_0`, the
  polar part of `g_n(y)v_0` agrees with `v_0` off an initial projection
  whose trace tends to zero. Fill that missing initial projection into the
  unused part of `g_n(y)`; `(DR8)` leaves at least `delta_0` of room.
  The resulting member of `Phi_n(y)` tends to `v_0` in `2`-norm.
  This also proves lower semicontinuity at the boundary, where
  `xi_n(y)->xi_n(y_0)`.
* **Uniform local connectivity.** After choosing one base frame, each full
  value in `(DR9)` is isometric to a strong Stiefel space in the II1
  factor `g_n(y)Ng_n(y)`. The normalized corner trace rescales the metric
  by `tau(g_n(y))^(-1/2)`. Since `tau(g_n(y))>=delta_0`, the universal
  modulus of `stw22-diffuse-stiefel-uniform-loop-fillings` gives one
  ambient equi-`LC^1` modulus for all the values. The degree-zero part also
  follows directly from principal-log paths.
* **Simple connectivity.** A loop of frames first lifts, by the
  one-dimensional continuous-comparison theorem of Farah--Vaccaro, to a
  loop in the unitary group of the target corner. Jekel's SOT contraction
  contracts that loop. Multiplication by the base frame fills the original
  loop. Singleton boundary values are trivially one-connected.

The operator-norm unit ball of `L^2(N)` is complete. Michael's
*Continuous Selections II*, Theorem 1.2, with `n=1`, applied to the
two-dimensional disk therefore gives a continuous selection `V_n` from
`(DR9)` which equals `xi_n` on the boundary. This is the relative
selection point: encoding the boundary values as singletons preserves
lower semicontinuity and forces the selected extension to be exact there.

## Orthogonal recursion and weighted limit

The selection above iterates because `(DR8)` holds at every stage. Define

```text
X_N(y)=sum_(n=0)^N V_n(y)b^(1/2)r_n.                    (DR10)
```

The final projections of the `V_n` are orthogonal, so, uniformly in `y`,

```text
||X_M(y)-X_N(y)||_2^2
 =sum_(N<n<=M)tau(br_n).                                (DR11)
```

Thus `X_N` converges uniformly in `2`-norm. Moreover
`X_N^*X_N<=b`, so the limit is an element of the operator-norm unit ball
of `N`, not merely an affiliated operator. Passing to the limit in
`L^1` gives `X^*X=b`, while `fX=X`. Equation `(DR6)` gives the
prescribed boundary exactly. Finally both `X(y)` and `x_0` have
`2`-norm `sqrt(tau(b))`, which proves `(DR4)`.

The external inputs are Farah--Vaccaro,
[*Continuous Selection of Unitaries in II1 Factors*](https://arxiv.org/abs/2501.01272),
Theorem 1.1 and its lower-semicontinuity argument; D. Jekel,
[*The unitary group of a II1 factor is SOT-contractible*](https://arxiv.org/abs/2508.05834),
Theorem A; and E. Michael, *Continuous Selections II*, Ann. of Math. 64
(1956), Theorem 1.2.
