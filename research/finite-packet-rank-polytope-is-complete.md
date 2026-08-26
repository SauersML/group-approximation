---
rg: 2
id: finite-packet-rank-polytope-is-complete
kind: claim
title: Finite semisimple packet ranks form a complete rational polytope
distinct_from:
  finite-corona-dimension-certificate-calculus: that decides whether homogeneous stable projection relations force one coordinate to vanish; this describes all normalized spectral-rank vectors of a semisimple packet and gives metric defect bounds and exact realization inside the feasible polytope.
  finite-packet-multiplicity-certificates-detect-mf-radicals: that combines subgroup restriction and conjugacy matrices to annihilate selected irreducible germs; this is the convex geometry of finitely many spectral reads after one packet and its common multiplicity state have already been authenticated.
artifacts:
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
---

**ESTABLISHED FINITE-DIMENSIONAL THEOREM.**  Let

```text
A = directSum_(alpha=1)^s M_(d_alpha)(C)
```

be a finite-dimensional semisimple C-star algebra.  A nonzero
finite-dimensional representation of `A` has multiplicities `m_alpha` and
dimension

```text
D=sum_alpha d_alpha m_alpha.
```

Its dimension-weighted sector state is

```text
p_alpha=d_alpha m_alpha/D,
p in Delta_(s-1).                                      (RPP1)
```

Fix `k` packet projections.  If the `i`-th projection has normalized rank
`q_(i,alpha)` in sector `alpha`, put `Q=(q_(i,alpha))`.  Every normalized
rank vector read from the packet is

```text
Qp in P_Q := Q Delta_(s-1)
            = conv{q^(1),...,q^(s)}.                   (RPP2)
```

Suppose source reflections have negative rank fractions `r_i`, the packet
reflections have rank vector `Qp`, and unitary covariance-row defects are

```text
delta_i=||W_i R_i W_i^*-T_i||_2.
```

Then

```text
|r_i-(Qp)_i| <= delta_i/2,                             (RPP3)

max_i delta_i >= 2 dist_infinity(r,P_Q),               (RPP4)

sum_i delta_i^2 >= 4 dist_2(r,P_Q)^2.                  (RPP5)
```

If `Q` and `r` are rational and `r` is outside `P_Q`, rational polyhedral
separation supplies `lambda in Q^k` and `gamma in Q_(>0)` with

```text
lambda.r >= max_(p in Delta) lambda.(Qp)+gamma.         (RPP6)
```

Every approximate realization then pays the machine-checkable defect

```text
sum_i |lambda_i| delta_i >= 2 gamma,
max_i delta_i >= 2 gamma/||lambda||_1.                 (RPP7)
```

The criterion is complete for rank-only arguments.  If rational `r` lies
in `P_Q`, there is a rational `p` with `Qp=r`; after one common
amplification all multiplicities `m_alpha=Dp_alpha/d_alpha` are nonnegative
integers, giving an exact finite-dimensional packet model with precisely
the demanded ranks.  Thus no argument using only this finite list of sector
masses, affine rank reads, direct sums, and amplifications can create a
uniform gap at a point inside `P_Q`.

Direct sums merely take convex combinations in `(RPP2)`.  Tensoring the
whole packet and every covariance row by an identity spectator changes
neither `p`, the rank vector, nor any normalized Hilbert--Schmidt defect.
Accordingly `P_Q` is exactly the envelope of all direct-sum and spectator
escapes.

**Shared-involution regression corollary.**  For rows sharing one
involution gauge, put `a_i=2q_i-1`, `b_i=1-q_i`.  Their predictions are
`b_i+a_i theta`, and

```text
sum_i delta_i^2
  >= 4 min_(theta in [0,1])
       sum_i (r_i-b_i-a_i theta)^2.                   (RPP8)
```

When every `a_i` is nonzero, write
`theta_i^*=(r_i-b_i)/a_i`, `w_i=a_i^2`, and let
`bar(theta)=sum_i w_i theta_i^*/sum_i w_i`.  If `bar(theta)` lies in
`[0,1]`, `(RPP8)` is four times the weighted regression variance

```text
sum_i delta_i^2
  >= 4 sum_i w_i(theta_i^*-bar(theta))^2.             (RPP9)
```

If the weighted mean lies outside `[0,1]`, clipping it to the nearest
endpoint gives the exact constrained minimum, which is at least the
unconstrained variance in `(RPP9)`.
