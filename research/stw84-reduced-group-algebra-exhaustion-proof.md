---
rg: 2
id: stw84-reduced-group-algebra-exhaustion-proof
kind: route
title: Realize an amenable group algebra as the inductive limit of subgroup algebras
target: stw84-directed-union-uniform-bound
requires: []
---

For an arbitrary subgroup `H subset G`, restriction of the left regular
representation of `G` to `H` is a direct sum of copies of the left regular
representation of `H`, indexed by the left cosets `H\G`.  Hence the canonical
map

```text
C*_r(H) -> C*_r(G)
```

is injective.  The union of the images of `C*_r(G_n)` contains every canonical
group unitary and is therefore dense in `C*_r(G)`.  Thus

```text
C*_r(G)=direct_limit_n C*_r(G_n).
```

Amenability passes to subgroups and identifies full and reduced group
C*-algebras for `G` and every `G_n`, giving the displayed full-algebra limit.

Nuclear dimension is upper semicontinuous for inductive limits.  Applying the
standard finite-set approximation proof to any cofinal subsequence on which
the dimensions realize their liminf gives the asserted inequality.

