---
rg: 2
id: coherence-passes-to-polycyclic-by-coherent-extensions-proof
kind: route
title: Intersect with the polycyclic kernel, push the rest into the coherent quotient, and extend presentations
target: coherence-passes-to-polycyclic-by-coherent-extensions
requires: []
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

Let `K <= G` be finitely generated.

1. `K ∩ N` is a subgroup of a polycyclic-by-finite group, so it is
   polycyclic-by-finite and hence finitely presented.
2. `K/(K ∩ N) ≅ KN/N <= Q` is finitely generated, so it is finitely
   presented because `Q` is coherent.
3. An extension of a finitely presented group by a finitely presented group
   is finitely presented (P. Hall).

So `K` is finitely presented. This is Lemma 1.1 of the artifact.
