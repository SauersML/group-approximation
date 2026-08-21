---
rg: 2
id: native-sl3-hecke-graph-wreath-identification-proof
kind: route
title: Eliminate all graph-wreath vertex generators except the base vertex
target: native-sl3-group-is-hecke-graph-wreath-product
requires:
  - native-sl3-commuting-involution-group
---

Present the semidirect product with the generators of `A` and generators
`c_(aC)` for all vertices.  The action relations are

```text
g c_(aC) g^-1 = c_(gaC).                               (ID1)
```

Transitivity lets us eliminate every vertex generator in favor of

```text
c=c_C,       c_(aC)=a c a^-1.                          (ID2)
```

The ambiguity in `(ID2)` is exactly right multiplication by `C`, and is
removed by `[c,s]=1` for a finite generating set `S_C`.  The vertex-group
relations reduce to `c^2=1`.  Finally every edge is an `A`-translate of
`{C,hC}`, so all edge commutators reduce to the single prototype

```text
[c,h c h^-1]=1.                                        (ID3)
```

After these Tietze eliminations the presentation is exactly `(GCC1)`, proving
`(HGW1)`.
