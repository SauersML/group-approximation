---
rg: 2
id: atlas-a8-439-forbidden-block-proof
kind: route
title: Minimize the deleted rectangle using the fourteen concrete A8 degrees
target: atlas-a8-hall-deficit-needs-439-forbidden-blocks
requires:
  - atlas-a8-mixed-block-transport-has-permutation-models
  - weighted-unitary-hall-deficit-gap
---

Let `T` be the complement of `N_E(S)` in the target vertex set.  Every pair
in `S times T` is forbidden, and `(H439-1)` is equivalent to

```text
w(S)+w(T)>20160.                                      (H439-4)
```

Write `s=|S|` and `t=|T|`.  The largest vertex weight in `(MBT1)` is `70`.
If `s,t>=2`, `(H439-4)` implies

```text
70(s+t)>20160,
```

so `s+t>=289`.  Among integers at least two with this sum, the product is at
least

```text
s t>=2*287=574>439.                                  (H439-5)
```

If `s=1`, then `w(S)<=70`, so Hall deficit gives `w(N_E(S))<70`.  The ten
smallest vertex weights are

```text
1, 7,7,7,7,7,7,7, 14,14,
```

because the degree-`7` irrep supplies seven minimal projections and the
degree-`14` irrep supplies fourteen.  The first nine sum to `64`, while the
first ten sum to `78`.  Hence a target set of weight below `70` has at most
nine vertices.  Therefore `t=448-|N_E(S)|>=439`, giving at least 439
forbidden pairs.  The case `t=1` is symmetric: `(H439-4)` makes the complement
of `S` have weight below `70`, hence at most nine vertices and `s>=439`.

These cases exhaust all possibilities and prove the lower bound.  The graph
described in `(H439-3)` deletes one rectangle of size `1*439` and realizes a
strict deficit, proving sharpness.

If at most 438 pairs are forbidden, the proved lower bound says the allowed
graph has no strict weighted Hall cut.  Give source and target vertex `v`
the integral capacity `d_v`.  The capacitated Hall/max-flow theorem supplies
a real flow with these full margins; total unimodularity of the bipartite
incidence matrix supplies an integral one.  Apply the basis-matching
construction in `(MBT3)--(MBT4)` with `k=1`.  Blocks on forbidden edges have
cell size zero, so the resulting permutation unitary satisfies `(H439-6)`.
This proves the exact absorber statement.
