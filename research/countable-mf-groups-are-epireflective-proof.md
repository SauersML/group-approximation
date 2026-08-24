---
rg: 2
id: countable-mf-groups-are-epireflective-proof
kind: route
title: Promote the universal radical quotient to its adjunction
target: countable-mf-groups-are-epireflective
requires:
  - universal-mf-quotient
  - mf-radical-functoriality
---

Functoriality gives

```text
f(Rad_MF(G)) <= Rad_MF(H),
```

so every homomorphism descends uniquely to the displayed map on radical
quotients.  Identities and compositions descend to identities and
compositions, making `R_MF` a functor.

The universal quotient theorem says `R_MF(G)` is MF and every map from `G` to
an MF group kills `Rad_MF(G)`.  It therefore factors uniquely through the
surjective unit `G->R_MF(G)`.  This factorization is natural in both
variables, which is precisely the adjunction.

For an MF group `M`, its radical is trivial, so the unit at `M` is an
isomorphism.  Hence applying the reflector twice changes nothing.  Every unit
is a quotient map, proving epireflectivity.
