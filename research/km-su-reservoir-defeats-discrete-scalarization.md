---
rg: 2
id: km-su-reservoir-defeats-discrete-scalarization
kind: claim
title: The Kac-Moody SU multiplicity reservoir defeats determinant rank and Schur scalarization tests
distinct_from:
  three-chart-loop-retains-free-multiplicity-holonomy: that leaves an arbitrary multiplicity unitary on an abstract chart loop; this places a near-identity special-unitary family on exact regular parahoric cores and computes the failure of each proposed finite-matrix invariant.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that gives a gap for a nonscalar fixed label relator; this keeps the finite label and its projective cocycle exactly trivial while the growing multiplicity holonomy is nonscalar and tends to the identity.
  km-kazhdan-holonomy-rounding-starts-after-projective-flatness: that identifies exact projective relator scalarization as the gate before property T applies; this proves determinant, rank cuts, divisibility, and finite Schur data cannot supply that gate with a dimension-free regular-core retention theorem.
---

Let a finite parahoric label packet act regularly on `L`, and amplify it by
`C^m`. Every local group-algebra matrix unit then has the form

```text
C_x tensor I_m.
```

For every even `m` and every `0<t<pi`, put

```text
W_(m,t)=diag(e^(it) I_(m/2),e^(-it) I_(m/2)) in SU(m). (KSR1)
```

Multiplying one overlap transporter by `I_L tensor W_(m,t)` preserves
exactly:

1. every finite parahoric representation and regular multiplicity;
2. every overlap-subgroup intertwining equation;
3. all dimension and divisibility data;
4. determinant one; and
5. the finite-label projective cocycle and Schur-multiplier class.

Nevertheless the returned multiplicity holonomy is nonscalar for `t!=0`,
while

```text
||W_(m,t)-I||_2^2=2-2cos(t) ->0                      (KSR2)
```

as `t->0`, uniformly in `m`. Moreover

```text
rank(W_(m,t)-I)=m.                                     (KSR3)
```

Thus arbitrarily small normalized-HS relator defect can have full-rank
support. Any scalarization method based on deleting the rank support loses
the entire regular core, even though an analytic perturbation of size
`O(t)` exists. Replacing `(KSR1)` by a diagonal special unitary with `m`
distinct phases in `[-t,t]` makes every reducing subspace on which the
holonomy is scalar have dimension at most one. Hence no dimension-free
large-corner scalarization follows from spectral multiplicity or divisibility
either.

This is a sharp impossibility for the proposed discrete mechanisms, not for
projective HS stability itself. Determinant and the finite Schur multiplier
see only scalar/projective data; rank and divisibility have no continuity in
normalized HS norm; and the exact regular parahoric cores commute with the
whole `SU(m)` reservoir. A successful scalarization theorem must analytically
couple the growing multiplicity gauge to several native face relations. It
cannot be a determinant phase choice, a bounded Schur-multiplier argument,
or a small-rank quarantine.
---
