---
rg: 2
id: hrf-sym4-composition-sector-kills-five-mark
kind: claim
title: Every pure Sym4 composition-sector representation kills the pinned triangle's central five-mark
distinct_from:
  hrf-amplified-sym4-five-twists-have-no-detectors: that assumes semisimple vertex restrictions and a scalar central mark; this allows arbitrary vertex extensions and an arbitrary central-mark matrix
  hrf-sym4-isotypic-modules-are-semisimple: that is a single-vertex representation theorem without edge relations; this applies it to the twisted triangle and proves annihilation of the mark
artifacts:
  - research/artifacts/hrf-sym4-extension-rigidity-2026-09-20.md
  - research/artifacts/hrf-amplified-2026-09-20.md
---

For the pinned central five-twisted PSL2(F19) triangle Lambda_d defined
in [[hrf-amplified-sym4-five-twists-have-no-detectors]], let d be nonzero.
Let K be any field of characteristic 19. Every finite-dimensional
representation of Lambda_d over K whose three vertex restrictions have
only Sym^4(K^2) as composition factors sends its central mark Z to I.

No semisimplicity assumption on the vertex restrictions and no scalar
assumption on Z are needed. Thus any characteristic-19 detector of Z
must use another vertex composition factor somewhere. This does not
exclude mixed sectors, other characteristics, or all finite detectors.

Proof: [[hrf-sym4-composition-sector-proof]].
