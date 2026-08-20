---
rg: 2
id: thompson-v-central-extensions-split-proof
kind: route
title: Acyclicity and universal coefficients split the Thompson extension
target: thompson-v-central-extensions-split
requires: []
artifacts:
  - research/artifacts/thompson-v-central-extension-splitting-2026-08-20.md
---

Szymik--Wahl prove that Thompson's group `V` is integrally acyclic, so in
particular `H_1(V,Z)=H_2(V,Z)=0`.  The universal-coefficient exact sequence

```text
0 -> Ext(H_1(V,Z),A) -> H^2(V,A) -> Hom(H_2(V,Z),A) -> 0
```

therefore gives `H^2(V,A)=0`.  This classifies central extensions with
trivial coefficient action, proving existence of a splitting.  Two splittings
differ by a homomorphism `V->A`, and every such homomorphism factors through
the zero abelianization `H_1(V,Z)`.  The splitting is therefore unique.
