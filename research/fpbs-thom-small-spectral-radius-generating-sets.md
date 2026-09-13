---
rg: 2
id: fpbs-thom-small-spectral-radius-generating-sets
kind: claim
title: Nonamenable groups have finite symmetric generating sets of arbitrarily small spectral radius
distinct_from:
  fpbs-simple-generating-set-with-gap-exists: that asserts strict percolation thresholds on one simple Cayley graph; this is Thom's operator-norm theorem, whose generating sets may contain the identity and which by itself says nothing about percolation.
artifacts:
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

**ESTABLISHED (imported).** Let `Gamma` be a finitely generated nonamenable
group. For every `epsilon > 0` there is a finite symmetric generating set
`S ⊂ Gamma` with `rho(S) < epsilon`. Here
`rho(S) = ||(1/|S|) sum_{s ∈ S} lambda(s)||`, the operator norm in the
left-regular representation. The theorem does not exclude `e ∈ S`.

A. Thom, *A remark about the spectral radius*, arXiv:1306.1767v1:
- Theorem 1 (page 2), second sentence;
- definitions of `m(S)` and `rho(S)` on page 1.

Read from the PDF on 2026-09-12. Corollary 8 of the same paper (page 5) derives
from this that some finite symmetric generating set has `p_c < p_u`. Its proof
is one sentence referring to Pak–Smirnova-Nagnibeda, so it is not imported
here.

Status records an imported theorem, not independent mathematical verification.
