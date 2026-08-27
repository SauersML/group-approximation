---
rg: 2
id: normal-kazhdan-kernel-amenable-edge-tree-proof
kind: route
title: Combine property FA, normality, minimality and the amenable edge stabilizer
target: normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree
requires: []
---

Property `(T)` implies Serre's property `FA`.  After barycentrically
subdividing to remove inversions, the restricted action of `K` on `T`
therefore has a fixed vertex.  Its fixed-point set

```text
T^K={x in T : kx=x for every k in K}
```

is a nonempty subtree.  Normality makes this subtree `G`-invariant: for
`g in G`,

```text
g T^K = T^(gKg^(-1)) = T^K.
```

Minimality of the `G`-action now gives `T^K=T`.  Thus `K` fixes every edge
pointwise and is contained in every edge stabilizer.  Choose one edge `e`.
Since `G_e` is amenable, its subgroup `K` is amenable.  An amenable discrete
property-`(T)` group is finite.  If `G_e` is torsion-free, its only finite
subgroup is trivial, proving `(AKT1)`.

For a nondegenerate amalgam `A *_C B`, the Bass--Serre action is nontrivial
and minimal, and the edge stabilizers are conjugates of `C`.  The same holds
for a nondegenerate HNN extension.  Taking `C` amenable proves the announced
closure obstruction.  In Kar--Nikolov's construction `C=Z`, so the conclusion
is triviality even though the two ambient arithmetic vertex groups themselves
contain torsion.

Primary source for `(AKT2)` and its soficity:

```text
A. Kar and N. Nikolov, A non-LEA Sofic Group,
arXiv:1405.1620v4, Theorem 1.
https://arxiv.org/abs/1405.1620
```

