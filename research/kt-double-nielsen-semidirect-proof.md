---
rg: 2
id: kt-double-nielsen-semidirect-proof
kind: route
title: Compute the fold covering graph and its affine deck action
target: kt-double-is-nielsen-semidirect-product
requires: []
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

Let `r:D->G` be the fold retraction, equal to the identity on both vertex
groups, and let `K=ker(r)`.  The map `r` is injective on every conjugate of a
vertex group.  Hence `K` has trivial vertex stabilizers in the Bass--Serre
tree `T` of `D` and acts freely on `T`.

The quotient graph `K\T` has two vertices.  Its unoriented edges are indexed
by

```text
(D/K)/(Gamma K/K)=G/Gamma=X.                   (KNP1)
```

Choose the edge `o=Gamma` as a maximal subtree.  The fundamental group of
this two-vertex, `X`-edge graph is free on the loops

```text
b_x=e_x e_o^(-1),                 x in X-{o}.   (KNP2)
```

Since `K` is the deck group, `(KNP2)` identifies `K` with
`N=F({b_x:x!=o})`.  The first vertex copy of `G` splits `r`, so

```text
D=K semidirect G.                                (KNP3)
```

The splitting acts on `K\T` by left translation of the edge labels.  It
sends the loop `e_x e_o^(-1)` to `e_(g x)e_(g o)^(-1)`.  Rewriting with
`e_y e_o^(-1)=b_y` gives

```text
g b_x g^(-1)=b_(g x)b_(g o)^(-1),               (KNP4)
```

which is `(KNS1)--(KNS2)`.

For every discrete semidirect product `N semidirect_alpha G`, the left
regular representation identifies its reduced group C-star algebra with the
reduced crossed product `C*_r(N) crossed_(alpha,r) G`: on
`ell2(N) tensor ell2(G)` the two regular covariant representations agree on
the canonical group unitaries.  This identification preserves the
coefficient-of-the-identity trace, proving `(KNS3)`.
