---
rg: 2
id: sofic-factor-products-via-quantitative-surjunctivity
kind: route
title: Transplant along sofic models of the second factor and bound the stored defect by the quantitative deficit of the first
target: products-with-a-sofic-factor-are-surjunctive
requires:
  - surjunctive-groups-are-quantitatively-surjunctive
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

Theorem Q, Section 3 of the artifact.

1. **The subshift.** A Garden of Eden pattern `p` on `E <= G x K`, with `K`-coordinates `E_K`, defines the
   proper subshift `Y` of `(A^(E_K))^G` avoiding `p` at every `G`-translate.
2. **The map.** For a `(P, epsilon)`-model `V` of `K`, the transplant with stored bad points is an injective
   automaton over `G`. It maps `((A^(E_K))^n x A^|R|)^G` into `Y^n x (A^(|R| + epsilon |V|))^G`, with
   `n >= (1 - epsilon)|V| / (|E_K|^2 + 1)` disjoint good blocks.
3. **Conclusion.** Quantitative surjunctivity of `G` forbids this once `epsilon` is small relative to
   `delta_Y`.
