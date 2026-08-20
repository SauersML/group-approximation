---
rg: 2
id: finite-free-phase-product-embedding-has-an-injective-coordinate
kind: claim
title: A faithful finite product of free-phase maps has a faithful coordinate
distinct_from:
  graph-endomorphism-phase-hnn-embeds-formanek-procesi: that assumes one coordinate is the identity and the others come from ambient endomorphisms; this proves that every injective map into finitely many commuting free factors has some injective coordinate, but does not extend the remaining partial maps to the ambient factor.
  diagonal-hnn-exactly-advances-free-phase-depth: that studies the explicit diagonal map into two copies; this is a structural theorem for every finite tuple of homomorphisms.
  infinite-edge-common-commutant-for-first-chord: that seeks an asymmetric nonamenable transport; this rules out making the transport jointly faithful from finitely many individually lossy phase coordinates.
---

Let `F` be a nontrivial finite-rank free group and let

```text
delta=(theta_1,...,theta_m):F -> F_1 times ... times F_m  (FPC1)
```

be a homomorphism to a finite product of free groups.  If `delta` is
injective, then at least one coordinate homomorphism `theta_i` is injective.

Consequently every injective finite-layer phase transport has a graph normal
form over one faithful coordinate.  After choosing such a coordinate, its
image is

```text
{(x,psi_2(x),...,psi_m(x)) : x in theta_i(F)},           (FPC2)
```

where the `psi_j` are homomorphisms defined on the embedded subgroup
`theta_i(F)`.  The only freedom not covered by the existing
Formanek--Procesi graph-endomorphism fence is therefore **partial** graph data:
one or more `psi_j` must fail to extend to endomorphisms of the whole ambient
free factor (or the transport must cease to be a finite product of commuting
free-phase coordinates).

In particular, adding more finitely many commuting phase layers cannot create
a faithful transport whose information is invisible in every individual
layer.
