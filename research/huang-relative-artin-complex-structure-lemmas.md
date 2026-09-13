---
rg: 2
id: huang-relative-artin-complex-structure-lemmas
kind: claim
title: "Huang: relative Artin complexes are simply connected on at least three types, have typed links, carry a poset structure along paths, and are bowtie free in spherical type"
distinct_from:
  haettel-flag-poset-contractibility-criterion: that is a contractibility criterion for abstract typed complexes; this collects the structural facts about Artin complexes that feed it.
---

Let `Λ` be a Coxeter diagram with Artin complex `Δ_Λ`, and for an induced subdiagram `Λ'` let
`Δ_{Λ,Λ'}` be the induced subcomplex on vertices of types `ŝ`, `s ∈ Λ'`.

1. **Simple connectivity.** If `|Λ'| ≥ 3`, then `Δ_{Λ,Λ'}` is simply connected.
2. **Links.** For a vertex `v ∈ Δ_{Λ,Λ'}` of type `ŝ`, there is a type-preserving isomorphism
   `lk(v, Δ_{Λ,Λ'}) ≅ Δ_{Λ−{s}, Λ'−{s}}`. When `Λ − {s}` is disconnected, `Δ_{Λ−{s}}` is the
   join of the Artin complexes of the components.
3. **Poset structure.** If `Λ' = s_1 ⋯ s_n` is an admissible linear subgraph of `Λ`, the
   relation `<` on the vertices of `Δ_{Λ,Λ'}` induced from `s_1 < ⋯ < s_n` makes them a weakly
   graded poset.
4. **Bowtie freeness.** If `Λ` is irreducible spherical and `Λ'` is a linear subdiagram, then
   `Δ_{Λ,Λ'}` is bowtie free.
5. **Rank two girth.** If `Λ` is a single edge labelled `m`, then the bipartite graph `Δ_Λ` has
   girth at least `2m`.
6. **Meets and joins.** In a weakly graded bowtie-free poset, two elements with a common upper
   bound have a join, and two elements with a common lower bound have a meet.

Literature import through `huang-relative-artin-complex-structure-lemmas-citation`.
