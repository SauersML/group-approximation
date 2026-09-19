---
rg: 2
id: pauli-cycle-overlap-countermodel-proof
kind: route
title: Put X and Z on two macroscopic disjoint cycle sectors
target: two-copy-overlap-consistency-has-pauli-cycle-countermodel
requires: []
---

For each even `N`, split the vertex set into equal parts `V_X,V_Z`.  Put a
cycle through each part and add a fixed number of random regular bipartite
matchings between the parts.  With positive probability the resulting
bounded-degree graph has a uniform spectral gap; fix any such realization.
The two within-part cycles are vertex-disjoint and each contains a constant
fraction of all edges.

On `C^2`, assign one reflection to every edge:

```text
Q_e = sigma_X  for e on the V_X cycle,
Q_e = sigma_Z  for e on the V_Z cycle,
Q_e = I        for every cross edge.                         (PCO1)
```

At a vertex of `V_X`, exactly two incident reflections are `sigma_X` and the
rest are identities.  They commute and their product is `I`.  The analogous
statement holds with `sigma_Z` on `V_Z`.  Hence every star admits a joint PVM
supported on the local even-parity code.  Use that PVM as the local-view
answer.  Both endpoint views induce the same reflection `(PCO1)` on their
shared edge, so every overlap consistency test is passed exactly.

Nevertheless a cycle edge in `V_X` anticommutes with every cycle edge in
`V_Z`.  Since both cycles have linear size, a constant fraction of uniformly
random ordered edge pairs anticommute.  No common PVM or commuting global
reflection table can agree with this exact strategy.

In label language, the two cycle indicators are classical global sections
whose restrictions to each vertex star have rank at most one, but their Pauli
labels span a symplectic two-plane globally.  This identifies the missing
condition as expansion of the exterior-square/local-rank-two sheaf, not
ordinary graph Poincare expansion.

