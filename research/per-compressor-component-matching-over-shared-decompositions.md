---
rg: 2
id: per-compressor-component-matching-over-shared-decompositions
kind: claim
title: The Kun--Thom component matching holds for every compressor over one sofic approximation and one pair of expander decompositions
artifacts:
  - GroupApproximation/KunThom/CompressorMatching.lean
---

**Setting.**
- `D : LocalCriterionData G Γ PUnit` carries a compression setup, a sofic
  approximation `A` of `G`, an expander decomposition of `A` restricted to `Γ`,
  and an ambient expander decomposition of `A`.
- For a compressor `t` of the setup, `D.withDistinguished t ht` keeps `A` and both
  decompositions and makes `t` the distinguished compressor. Put `q = A_n(t)`.

**Statement (Lean, `GroupApproximation.LocalCriterionData`).** Let `D_n` be the
acceptable components of `D.withDistinguished t ht` at its matching threshold
`η_n`. Past the matching start of `t`:
1. `refineIndex_injOn_acceptable`: the dominant target map `refineIndex q` is
   injective on `D_n`.
2. `refinement_sourceDefect_le`: for `B ∈ D_n`, the overlap arrow
   `refinementPartialBijection q B` misses at most `η_n |B|` source points. This
   holds at every `n`.
3. `image_symmDiff_refineIndex_le` bounds `|q(B) ∆ (refineIndex q B)|`, and
   `refinement_targetDefect_le` bounds the missing target mass. Both bounds are
   `matchingCoefficient η_n · |B|`, and `matchingCoefficient η_n → 0`.
4. `discarded_negligible`: the components outside `D_n` carry `o(|Y_n|)` mass.
5. `badCluster_negligible`: the components that are not cluster-good carry `o(|Y_n|)`
   mass.

The per-compressor statements use `(D.withDistinguished t ht).matchingStart`,
not a shifted index. So finitely many compressors share every index past the
largest start.

**Not covered here.**
- The mass outside the image `π_n(D_n)` of the targets.
- The localized label error of `u_n α_n(s) u_n⁻¹` against a word for `t s t⁻¹`.
- A `BlockPatching.BlockEmbedding` of the component partition.
