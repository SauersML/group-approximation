---
rg: 2
id: finite-packet-rank-polytope-proof
kind: route
title: Project normalized irreducible multiplicities and apply rational separation
target: finite-packet-rank-polytope-is-complete
requires: []
artifacts:
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
---

In sector `alpha`, one copy of the defining irreducible has dimension
`d_alpha`; hence the fraction of the total carrier lying in that sector is
`p_alpha=d_alpha m_alpha/D`.  Ranks add across the isotypic direct sum, so
the `i`-th packet projection has total normalized rank

```text
sum_alpha q_(i,alpha)p_alpha=(Qp)_i.
```

This proves `(RPP1)--(RPP2)`.

For row `i`, let `P_i=(1-R_i)/2` and `S_i=(1-T_i)/2`.  Then

```text
||W_i P_i W_i^*-S_i||_2=delta_i/2.
```

Cauchy--Schwarz for normalized trace gives

```text
|r_i-(Qp)_i|
 =|tau(W_i P_i W_i^*-S_i)|
 <=delta_i/2.
```

Taking the maximum and Euclidean norm and then minimizing over the actual
`p in Delta_(s-1)` proves `(RPP3)--(RPP5)`.

If `r` is outside the compact convex polytope `P_Q`, strict separation gives
`(RPP6)`.  Rational input permits a rational separator by the rational form
of Farkas' lemma.  For the actual `p`,

```text
gamma
 <= lambda.(r-Qp)
 <= sum_i |lambda_i| |r_i-(Qp)_i|
 <= (1/2)sum_i |lambda_i|delta_i,
```

which proves `(RPP7)`.

If rational `r` belongs to the rational polytope, the feasible system

```text
Qp=r,  p>=0,  sum_alpha p_alpha=1
```

has a rational point.  Choose `D` divisible by all denominators of the
numbers `p_alpha/d_alpha`; then `m_alpha=Dp_alpha/d_alpha` are nonnegative
integers and their packet direct sum realizes `r` exactly.  Direct sums act
on `p` by dimension-weighted convex combination.  Tensor spectators multiply
all ranks and the total dimension by the same integer, and normalized trace
factorization gives `||X tensor I_N||_2=||X||_2`.  This proves completeness
and the two invariance assertions.

For a shared involution, its positive spectral fraction `theta` gives

```text
(Qp)_i=1-q_i+(2q_i-1)theta=b_i+a_i theta.
```

Squaring `(RPP3)`, summing, and minimizing over `theta in [0,1]` proves
`(RPP8)`.  Ordinary one-variable least squares gives the weighted mean and
variance formula `(RPP9)`; convexity puts a constrained minimizer outside
the interval at its nearest endpoint.
