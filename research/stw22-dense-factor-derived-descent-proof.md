---
rg: 2
id: stw22-dense-factor-derived-descent-proof
kind: route
title: Convert asymptotic norm density into expectation convergence and descend the scattered skeleton
target: stw22-dense-factor-fields-have-uniform-traces
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-asymptotically-dense-factor-field-audit-2026-08-30.md
---

## Nuclearity and trace boundary

Evaluation at `infinity` gives an exact sequence

```text
0 -> direct-sum_n^c0 D_(i,n) -> B_i -> U_i -> 0.        (ADF1)
```

Surjectivity on the right is exactly `(ADF)`: for any `u in U_i`, choose
`d_n in D_(i,n)` with `||d_n-u|| -> 0`.  The ideal and quotient in
`(ADF1)` are nuclear, so `B_i` is nuclear.  The countable `c_0`-sum is
separable, as is `U_i`; lifting countable dense sets through `(ADF1)` proves
that `B_i` is separable.  Finite minimal tensor products and quotients
preserve nuclearity, proving the assertion for `B_K`.

The fibre of `B_K` at `x in K` is

```text
C_x=tensor_i C_(i,x_i),
C_(i,n)=D_(i,n),       C_(i,infinity)=U_i.
```

It has a unique trace.  Disintegrate any trace on `B_K` over its central
copy of `C(K)`.  The fibre functional is tracial almost everywhere and is
therefore the unique trace of `C_x`.  Conversely these fibre traces
integrate against every probability measure.  Hence

```text
T(B_K)=Prob(K).                                         (ADF2)
```

This is the same direct central disintegration used in the established
finite Bratteli-cube theorem; no assertion about traces on the completion
has entered yet.

## The exact uniform completion

Let `N_(i,n)` and `N_x` be as in the claim.  Uniqueness of the trace on
each `D_(i,n)` makes its GNS von Neumann algebra a factor.  Equation
`(ADF2)` says that the uniform tracial norm is the supremum of the
coordinate `2`-norms, so the uniform completion embeds in the displayed
section algebra `M_K`.

For the reverse inclusion, let `a in M_K` be bounded and fix `epsilon>0`.
For each `x in K`, Kaplansky density in `N_x` gives `c_x in C_x` with
`||c_x||<=||a||` which is `2`-close to `a(x)`.  Evaluation
`B_K -> C_x` is surjective.  To see this on elementary tensors, a
finite coordinate admits a section supported only at that isolated point,
while at an infinite coordinate `(ADF)` supplies a norm-convergent tail;
finite sums and norm closure give the general case.  Choose
`s_x in B_K` with `s_x(x)=c_x` and
`||s_x||<=||c_x||+epsilon`.  The `2`-continuity of `a` and `s_x` gives a
neighbourhood `V_x` on which

```text
||a(y)-a(x)||_2 < epsilon,
||s_x(y)-c_x||_2 < epsilon.                             (ADF3)
```

Choose a finite subcover `V_(x_1),...,V_(x_l)` and a partition of unity
`(f_j)` subordinate to it.  Then
`sum_j f_j s_j` belongs to `B_K`, is uniformly `2`-close to `a`, and has
operator norm at most `||a||+epsilon`, where `s_j=s_(x_j)`.
Thus its bounded uniform `2`-completion is exactly `M_K`.

## Expectations converge to the identity

Let `E_(i,n):R_i -> N_(i,n)` be the trace-preserving conditional
expectation.  It is the orthogonal projection in `L^2(R_i)`.  Condition
`(ADF)` implies

```text
||E_(i,n)(z)-z||_2 -> 0       for every z in R_i.        (ADF4)
```

Indeed, approximate `z` in `2`-norm by `u in U_i`, then approximate `u`
in norm by an element of `D_(i,n)`.  The distance from `z` to
`L^2(N_(i,n))` therefore tends to zero, which is exactly `(ADF4)`.

For `x in X`, let `E_x:R -> N_x` be the tensor product of these
expectations, with the identity in every infinite coordinate.  For every
fixed `z in R`, the map `x |-> E_x(z)` is `2`-norm continuous: finite
coordinates are isolated, and continuity at an infinite coordinate is
`(ADF4)`.  In particular evaluation `M_K -> N_y` is onto, since this
section takes the value `z` at `y` whenever `z in N_y`.

More locally, if `t -> y` in `X` and `z in N_y`, then

```text
||E_t(z)-z||_2 -> 0.                                   (ADF5)
```

A coordinate finite at `y` is eventually fixed, while a coordinate
infinite at `y` is governed by `(ADF4)`.  There are only finitely many
coordinates.

## Derived-set descent

Put `K_0=K` and `K_(r+1)=(K_r)^(1)`.  Since
`X^(r)` consists of the points with at least `r` infinite coordinates,

```text
K_r subset K intersect X^(r),       K_(d+1)=emptyset.    (ADF6)
```

Fix a compatible metric.  If `Y=K_(r+1)` is nonempty, choose for each
`t in K_r\Y` a point `rho(t) in Y` with

```text
dist(t,rho(t)) <= 2 dist(t,Y).
```

For a bounded section `b` over `Y`, define

```text
(Lb)(t)=E_t(b(rho(t)))       (t in K_r\Y),
(Lb)(t)=b(t)                 (t in Y).                   (ADF7)
```

If `t -> y in Y`, then `rho(t)->y`; contractivity and `(ADF5)` give

```text
||E_t(b(rho(t)))-b(y)||_2
 <= ||b(rho(t))-b(y)||_2+||E_t(b(y))-b(y)||_2 -> 0.
```

Thus restriction from the section algebra over `K_r` onto that over `Y`
is surjective.

Fix `x in Y`.  Restriction induces a surjection of fibre gaps

```text
q_r:I_x(K_r) -> I_x(Y).                                 (ADF8)
```

Its kernel is bounded-trace-free.  Indeed, a positive kernel class may be
changed modulo the central norm-fibre ideal so that its representative `b`
vanishes on `Y`: on shrinking clopen annuli at `x`, cut by the supremum of
the operator norm of its restriction to `Y`.  Those suprema tend to zero.

For `c=(b-epsilon)_+`, Chebyshev's inequality and `2`-continuity at `x`
make the support of `c(t)` have trace at most `1/m` on a sufficiently small
neighbourhood.  Every point of `K_r\Y` is isolated in `K_r`, and `N_t` is
a finite factor.  Choose there, independently, `m` orthogonal equivalent
copies of the support and put the implementing partial-isometry sections
equal to zero on `Y`.  They are `2`-continuous because

```text
||u_j(t)c(t)^(1/2)||_2^2=tau_t(c(t)) <= ||b(t)||_2 -> 0
```

at `Y`.  A bounded positive trace `sigma` on `ker(q_r)` therefore satisfies

```text
m sigma(c) <= ||sigma||.
```

First let `m` tend to infinity and then `epsilon` to zero.  This kills
every bounded positive trace on the kernel of `(ADF8)`.

Iteration terminates by `(ADF6)` at an isolated point, whose gap is zero.
Hence every fibre gap of `M_K` is bounded-trace-free.  Applying the exact
fibre-gap criterion proves the trace formula in the claim.
