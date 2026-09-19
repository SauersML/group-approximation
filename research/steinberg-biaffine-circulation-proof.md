---
rg: 2
id: steinberg-biaffine-circulation-proof
kind: route
title: Identify chord marginals with the two endpoint boundary maps
target: steinberg-zero-marginal-space-is-biaffine-circulation
requires:
  - steinberg-tree-cuts-are-five-marginals
---

For fixed `(a,b)`, varying `c` runs through the `p` chord edges incident to
the point vertex `(a,b)`, hence its unsigned incidence sum is `P(a,b)`.  For
fixed `(c,d)`, the incident point vertices are

```text
(x,xc-d),                 x in F_p,
```

so the other endpoint sum is `H(c,d)`.  Negating the basis vectors on the
line side converts these two unsigned sums into the oriented boundary map

```text
partial:k[E] -> k[V_point] direct_sum k[V_line].      (SBCI3)
```

The graph is connected: two point vertices with different first coordinate
have a common incident line, while points with the same first coordinate
connect through any point having a different first coordinate; line
vertices then connect through their incident points.  Therefore
`rank(partial)=|V|-1=2p^2-1`.  Since `|E|=p^3`, rank-nullity gives
`(SBCI2)` and the exact sequence

```text
0 -> ker(P,H) -> k[E] -> k[V_point] direct_sum k[V_line] -> k -> 0.
```
