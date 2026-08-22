---
rg: 2
id: atlas-edge-folner-modules-miss-natural-type
kind: claim
title: Bass--Serre edge Folner modules stay one quarter away from the natural Atlas chart type
distinct_from:
  atlas-augmented-relations-have-unbounded-chart-width: that proves the chart-coset graph is infinite and locally finite; this shows that truncating its edge module cannot satisfy the required repeated-natural chart restriction.
  atlas-left-ideal-rank-nonwandering: that asks whether every marked repeated-natural module blocks wandering; this excludes the standard induced/free-edge family of candidate countermodels.
  atlas-fixed-formal-toeplitz-microstates-promote: that excludes stationary linear finite sections by specialization; this excludes Bass--Serre permutation/induced finite sections by a modular chart-rank invariant.
---

Let `A=A8=GL_4(F2)`, let `V=F2^4` be its natural module, and fix a
transvection `t in A`.  Then

```text
rank_V(t-I)/dim(V)=1/4.                                (EFM1)
```

On every finite free `F2[A]`-module `F2[A]^q`, one instead has

```text
rank(t-I)/dim(F2[A]^q)=1/2.                            (EFM2)
```

The same value `1/2` holds on a free `A`-orbit carrying any finite linear
fiber decoration: after an orbitwise gauge change its module is a direct sum
of regular modules.

Consequently, suppose finite-dimensional exact `A`-modules `E_n` contain an
`A`-invariant free summand of codimension `o(dim E_n)`.  For every repeated
natural module `V^(m_n)` of the same dimension and every change of basis
`S_n`,

```text
rank( rho_n(t)-S_n rho_V^(m_n)(t) S_n^-1 )/dim(E_n)
 >=1/4-o(1).                                           (EFM3)
```

Therefore the standard Bass--Serre construction cannot refute
`atlas-left-ideal-rank-nonwandering`: finite edge sets in the chart-coset
graph have free left actions of both chart factors in their bulk, and a
Folner boundary of vanishing density leaves the regular value `1/2` on both
charts.  Exactification or alteration on the boundary changes `(EFM2)` only
by its relative dimension and cannot reach the required natural value
`1/4`.

Equivalently, an induced-module countermodel must place positive density in
nonfree/nonregular chart cells.  Such density is not a negligible graph
boundary, so its augmented relator defects require a new cancellation
mechanism; ordinary finite-subgraph compression of the infinite
Bass--Serre quotient is ruled out before testing whether `I E=E`.

