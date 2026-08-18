---
rg: 2
id: spherical-one-shared-map-relation-extension
kind: claim
title: One already chosen spherical generator map extends across one new multiplication relation
---

Fix one relation `gh=k` in a finite unitary table.  Suppose one of the three
partial generator bijections has already been chosen on `1-o(1)` of a sphere
cloud and tracks its unitary label with pointwise error at most `e` there.
For every `rho>0`, assume the normalized-HS relation defect tends to zero.
Then, after discarding `o(N)` roots, one can choose one of the two new label
maps from a radius-`rho` near-perfect matching and define the remaining map by
**exact composition**, obtaining partial bijections on `1-o(1)` of the cloud
such that

```text
sigma_g sigma_h = sigma_k
```

exactly on their common domain.  The newly forced map tracks its unitary label
with pointwise error at most

```text
e + 2 rho
```

outside `o(N)` roots.

The statement is symmetric in which of `g,h,k` is the already chosen map.
Thus a relation that meets an existing partial Schreier system in only one
label creates no synchronization obstruction; only repeated/cyclic reuse of
several already chosen labels can do so.
