---
rg: 2
id: fpbs-regular-tiling-edge-isoperimetric-constant
kind: claim
title: A planar regular graph with regular dual has an explicit edge isoperimetric constant
distinct_from:
  fpbs-expansion-thinning-threshold: that bounds p_c by one over one plus the edge expansion of any graph; this computes the edge expansion exactly for planar regular graphs with regular dual.
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

**ESTABLISHED (import).** Let `G` be a planar regular graph whose planar dual
`G†` is regular, with vertex degree `d_G` and face degree `d_(G†)`, and
`(d_G - 2)(d_(G†) - 2) > 4`. Then `G` is transitive and

```text
inf{ |∂_E K| / |K| : K ⊂ V(G) finite nonempty }  =  (d_G - 2) sqrt(1 - 4/((d_G - 2)(d_(G†) - 2))),
```

where `∂_E K` is the set of edges with exactly one endpoint in `K`.

For the Cayley graph of the genus-`g` surface group with standard generators,
the `{4g,4g}` tiling, this gives `sqrt((4g-2)^2 - 4)`.

Source: Häggström–Jonasson–Lyons, *Explicit isoperimetric constants and phase
transitions in the random-cluster model*, arXiv:math/0008191v2, Theorem 4.1 and
Remark 4.2, together with the identity `ι'_E = ι_E` for transitive graphs quoted
there from Benjamini–Lyons–Peres–Schramm. Route:
`fpbs-regular-tiling-edge-isoperimetric-constant-citation`.
