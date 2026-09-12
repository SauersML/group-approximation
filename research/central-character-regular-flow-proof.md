---
rg: 2
id: central-character-regular-flow-proof
kind: route
title: Restrict the central-character regular summand along every edge
target: central-character-regular-flow-defeats-finite-d8-return
requires: []
---

For `g in G_v`, the character of `q_chi l2(G_v)` is

```text
Tr(q_chi lambda_(G_v)(g))
 = |G_v|/|Z| chi(g),       g in Z,
 = 0,                      g notin Z.                  (CCP1)
```

Indeed, after expanding `(CCF1)`, the regular trace of the summand indexed by
`z` is nonzero exactly when `zg=1`.  Since an injective edge map is the
identity on `Z`, an element of `H_e` lands in `Z` exactly when it already
belongs to `Z`.  Comparing `(CCP1)` for `G_v` and `H_e` gives

```text
Res_(H_e)(q_chi l2(G_v))
  isomorphic to [G_v:H_e] q_chi l2(H_e).               (CCP2)
```

Multiplication by `L/|G_v|` turns the right side into
`(L/|H_e|) q_chi l2(H_e)`, independently of the endpoint.  The dimensions
are also independent of `v`:

```text
dim V_v=(L/|G_v|)(|G_v|/|Z|)=L/|Z|.                   (CCP3)
```

Choose a spanning tree and conjugate the vertex representations successively
so that the two edge copies agree on every tree edge.  On each chord choose
any unitary intertwiner supplied by `(CCF3)`.  The universal property of the
fundamental group of a graph of groups gives a finite-dimensional
representation with the claimed central character.  For `Z=<K>` and
`chi(K)=-1`, `(1-K)/2` is the identity.

