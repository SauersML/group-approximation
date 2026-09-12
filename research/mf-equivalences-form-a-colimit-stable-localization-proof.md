---
rg: 2
id: mf-equivalences-form-a-colimit-stable-localization-proof
kind: route
title: Invert exactly the maps inverted by the MF reflector
target: mf-equivalences-form-a-colimit-stable-localization
requires:
  - countable-mf-groups-are-epireflective
  - mf-reflection-colimit-calculus
---

The adjunction identifies `(ME1)` with invertibility of `R_MF(f)` by the
Yoneda criterion inside the full reflective subcategory.  The first item now
follows because isomorphisms have two-out-of-three and are closed under
retracts.

Colimits in the arrow category are computed objectwise.  Since `R_MF`
preserves every countable colimit under consideration, reflecting the
colimit of an objectwise MF-equivalence gives the colimit of a diagram of
isomorphisms, hence another isomorphism.  This proves items 2 and 3.

Let `f:G->H` be onto.  If `ker(f)<=Rad_MF(G)`, every map from `G` to an MF
group kills the kernel and factors uniquely through `H`; `(ME1)` follows.
Conversely, if `f` is an MF-equivalence, the composite

```text
G -> H -> R_MF(H)
```

has kernel containing `ker(f)`.  Under the isomorphism of reflections this
composite has the same kernel as the unit `G->R_MF(G)`, so
`ker(f)<=Rad_MF(G)`.

An idempotent reflector exhibits its essential image as the localization at
the morphisms it inverts, proving item 5.  Finally `A->1` is inverted exactly
when `R_MF(A)=1`.  Pushout and iterated-colimit stability give the last
assertions.
