---
rg: 2
id: lot-complexes-with-at-most-seven-vertices-are-aspherical
kind: claim
title: Every labelled oriented tree complex with at most seven vertices is aspherical, by an exhaustive census certified with primary-source asphericity tests
distinct_from:
  lot-complexes-with-at-most-six-vertices-are-aspherical: that covers at most six vertices with two criteria only; this adds the seven-vertex census, which needs the I-test, weight tests, local indicability on Tietze presentations and the relative test.
  contractible-2-complex-minus-a-cell-is-aspherical: that is the open finite one-cell case of Whitehead's conjecture, which contains every LOT complex; this settles only LOT complexes with at most seven vertices.
artifacts:
  - research/artifacts/hl-whitehead-lot-certify-2026-09-14.md
---

**ESTABLISHED** through `lot-at-most-seven-vertices-census-proof`.

**Claim.** Notation as in `lot-complexes-with-at-most-six-vertices-are-aspherical`. If the
labelled oriented tree Γ has at most seven vertices, then K(Γ) is aspherical.

**What the census found.** It covers 279943 classes of reduced seven-vertex LOTs.
- 279930 of them pass a presentation-level test (injective, one-cycle, I-test, weight test, or
  local indicability on a label presentation) or the relative test.
- The remaining 13 need a longer Tietze elimination sequence before Barreto--Minian Theorem 2.5
  applies. No common structural feature of these 13 has been identified.

**Novelty.** Not verified; a small-vertex census of LOTs may already be in print.
