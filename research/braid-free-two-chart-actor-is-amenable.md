---
rg: 2
id: braid-free-two-chart-actor-is-amenable
kind: claim
title: Separating the two Jacobi parabolics removes the braid only by losing relative-T expansion
distinct_from:
  jacobi-drifted-braid-defect-is-extensive: that shows why the two parabolics cannot be transported together; this analyzes the minimal duplicated-chart repair and shows that its actor becomes amenable.
  no-linear-symplectic-splitting-of-truncated-weyl-levels: that is a module-theoretic obstruction; this is a group-action/relative-property-T obstruction after duplicating the module charts.
---

Consider the minimal braid-free two-chart repair.  Put the upper additive
root group `U^+(R)` on the `Q` chart, put an independent lower additive root
group `U^-(R)` on the `P` chart, and let the coordinate-swap involution `F`
exchange the two chart/root pairs.  Impose no mixed rank-one braid.  The
image of the resulting actor is

```text
D=(R,+)^2 semidirect C_2,                                  (BFA1)
```

where `C_2` exchanges the two additive factors.  In particular `D` is
metabelian and amenable.

Let `N` be any infinite discrete Heisenberg or abelian Weyl group on which
this duplicated actor acts, with each root group confined to its own chart.
Then

```text
D semidirect N                                             (BFA2)
```

is amenable, and the pair `(D semidirect N,N)` does not have relative
property `(T)`.

Thus the simplest escape left by
`jacobi-drifted-braid-defect-is-extensive` is incompatible with the uniform
Clifford-expander input of `jacobi-congruence-clifford-tower`.  Keeping the
upper and lower charts independent avoids the extensive braid cocycle, but
also removes exactly the nonamenable mixed elementary action responsible for
relative `(T)`.  A viable stabilized construction must cancel the extensive
cocycle while retaining a genuinely mixed, nonamenable actor; mere chart
duplication is not enough.

