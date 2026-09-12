---
rg: 2
id: lef-criteria-miss-sequential-kun-thom-normalization-proof
kind: route
title: Read the hypotheses and conclusions of the LEF criteria against the per-compressor core, and exhibit the halving isotropy cycle
target: lef-criteria-miss-sequential-kun-thom-normalization
requires: []
artifacts:
  - research/artifacts/kt41-alt-route-2026-09-12.md
---

1. **Items 1 and 2.** These are readings of the landed statements:
   - `KunThom/KunThomTheorem.lean` and `KunThom/KunThomEssential.lean`;
   - `Criterion/CriterionAssembly.lean` and `Criterion/SelectionOutput.lean`;
   - `KunThom/NormalizationProducer.lean`.

   The artifact, sections 1 and 2, gives each hypothesis and where it fails.
2. **Item 3.** Each listed module concludes by comparing an exact cardinality or
   dimension (artifact, section 3). The recorded transfers to approximate settings
   stop where the graph says:
   - rank metric: `linear-scale-rank-conservation-does-not-kill-defects`;
   - tracial ultraproduct: `kt-centralizer-normalization-hs`, open.
3. **Item 4.** A direct computation over the cycle `i_0 -> i_1 -> ... -> i_(L-1) -> i_0`
   with `k(i_j) = 2^(L-1-j)`, all masses `1/L` and all sizes `2^L` (artifact, section 4).
   - For `1/k`, the summed changes are at most `1`, times `1/L`, plus a jump of at
     most `1/L`.
   - For `k/|C|`, they are at most `1/2` times `1/L`, plus a jump of at most `1/(2L)`.
