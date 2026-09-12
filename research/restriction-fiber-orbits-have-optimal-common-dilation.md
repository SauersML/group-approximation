---
rg: 2
id: restriction-fiber-orbits-have-optimal-common-dilation
kind: claim
title: Restriction-fiber endpoint orbits have an optimal quadratic common dilation
distinct_from:
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies the orbits and compares their same-dimensional HS distance; this computes the exact minimal flexible padding which merges two distinct orbits.
  congruence-cross-type-mixing-has-uniform-polar-repair: that extracts a large common endpoint intertwiner from an approximate unitary; this is the exact representation-semigroup geometry before any approximate intertwiner is supplied.
  core-expectation-misses-exact-endpoint-zero-modes: that shows a fixed linear expectation erases exact zero modes; this proves those nonlinear zero modes nevertheless have a complete stabilized metric.
---

Let `Q` be a finite congruence endpoint quotient, `K<Q` its square-free
core image, and let `m,n` be exact `Q`-representation multiplicity vectors
with the same `K`-restriction and common physical dimension `d`.  Define

```text
a=min(m,n),       p=m-a,       q=n-a,
k=|p|_dim=|q|_dim,
mu=k/d=(1/(2d)) sum_gamma dim(gamma)|m_gamma-n_gamma|.
                                                               (RFD1)
```

Then `res(p)=res(q)`, and cross-padding gives the identical exact type

```text
m+q=n+p=a+p+q.                                      (RFD2)
```

The enlarged cores agree, each side adds `k=mu d` dimensions, and the
padding fraction is

```text
k/(d+k)=mu/(1+mu).                                   (RFD3)
```

This is optimal.  If nonnegative endpoint types `u,v` satisfy
`m+u=n+v`, then `v` contains the positive part `p` of `m-n` and `u`
contains the negative part `q`; each added physical dimension is at least
`k`.

If `Delta` is normalized-HS distance between the two core-commutant
endpoint orbits, the uniform congruence gap gives

```text
kappa sqrt(mu)<=Delta<=2 sqrt(mu).                    (RFD4)
```

Hence close exact fibers merge through an exact larger endpoint at
quadratic cost, `mu<=Delta^2/kappa^2`, while fixed separation forces
`mu>=Delta^2/4`.

This resolves distinct exact fibers after authentication, including the
mod-three pair.  There is no positive relator-energy floor between them:
all their points have zero energy.  The correct alternative is stable
merging, and it always holds with optimal quadratic padding.  The remaining
global problem is selecting a nearby nonnegative fiber point from a raw
approximate endpoint before its quotient type is known.

