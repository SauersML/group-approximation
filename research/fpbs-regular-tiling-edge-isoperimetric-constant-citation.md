---
rg: 2
id: fpbs-regular-tiling-edge-isoperimetric-constant-citation
kind: route
title: Häggström–Jonasson–Lyons Theorem 4.1 computes the edge isoperimetric constant of regular tilings
target: fpbs-regular-tiling-edge-isoperimetric-constant
requires: []
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

Read on MSI on 2026-09-12 from the arXiv PDF of math/0008191v2, extracted with
`pdftotext`, Section 4, pages 17–19.

* **Definitions (page 17).** `∂_E K := E*(K) \ E(K)`, where `E(K)` is the set of
  edges with both endpoints in `K` and `E*(K)` the set of edges with at least
  one endpoint in `K`.
  `ι'_E(G) := lim_(N->infinity) inf{ |∂_E K|/|K| ; K ⊂ V, G(K) connected, N <= |K| < infinity }`.
* **Transitive case (page 17).** "It is shown in [4] that when G is transitive,
  ι'_E(G) = inf{ |∂_E K|/|K| ; K ⊂ V finite and nonempty }." Reference [4] is
  Benjamini–Lyons–Peres–Schramm.
* **Theorem 4.1 (page 17), verbatim up to typesetting.** "If G is a planar regular
  graph with regular dual G†, then ι'_E(G) = (d_G − 2) sqrt(1 − 4/((d_G − 2)(d_(G†) − 2)))."
* **Remark 4.2 (page 18).** "In this case, G and G† are transitive." The remark
  proves this by identifying the edge graph with that of a tessellation by
  congruent polygons.

Combining the transitive identity with Theorem 4.1 gives the target.

**Cross-check.** The same PDF extraction session read Lyons–Peres, *Probability
on Trees and Networks*, Theorem 6.18: "If G is an infinite, plane, regular graph
with regular dual G†, then Phi_E(G;1;1) = (d_G − 2) sqrt(1 − 4/((d_G − 2)(d_(G†) − 2)))."
Here `Phi_E(G;1;1)` is the infimum over finite nonempty `K` of `|∂_E K|/|K|`, so
this is the target statement directly.

**Specialization.** The Cayley graph of `Gamma_g`, `g >= 2`, for
`{a_i^(±1), b_i^(±1)}` is the 1-skeleton of the `{4g,4g}` tiling, a standard fact
not re-read here. With `d_G = d_(G†) = 4g`:
`(4g-2) sqrt(1 - 4/(4g-2)^2) = sqrt((4g-2)^2 - 4)`.
