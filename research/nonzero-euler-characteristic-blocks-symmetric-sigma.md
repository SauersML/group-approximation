---
rg: 2
id: nonzero-euler-characteristic-blocks-symmetric-sigma
kind: claim
title: "A type F group with nonzero Euler characteristic has no antipodal pair in Sigma^d(G;Z) for d >= cd G"
distinct_from:
  g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class: that claim is about when a product G x H is of type F through the Wall finiteness class; this one is about BNSR invariants of a single type F group, i.e. which maps to Z have FP kernels
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part1.md
---

Let `G` be a group of type F with Euler characteristic `e(G) ≠ 0`, and let
`d ≥ max(1, cd G)`. Then `Σ^d(G;ℤ) ∩ −Σ^d(G;ℤ) = ∅`. Consequently
`Σ^m(G) ∩ −Σ^m(G) = ∅` for all `m ≥ d`, and no epimorphism `G → ℤ` has a
kernel of type FP.

The proof combines three results: openness of `Σ^m(G;ℤ)` and the
FP_m-kernel criterion (Bieri–Renz 1988), density of rational character
classes, and multiplicativity of the Euler characteristic in extensions of
FP groups (Brown, *Cohomology of Groups*, VIII.6.1 and IX.7.3). See
`research/artifacts/zp-graph-braid-sigma-2026-09-13-part1.md` §2.
