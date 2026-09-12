---
rg: 2
id: kassel-four-cell-has-exact-omega-model
kind: claim
title: The minimal mixed Kassel four-cell has an exact 24-dimensional omega-sector model
artifacts:
  - research/artifacts/kassel-four-cell-exact-omega-model-2026-08-21.md
distinct_from:
  kassel-four-cell-is-minimal-determinant-holonomy: that locates the support-minimal scalar determinant identity; this proves that the same four faces have zero matrix relator energy in a nontrivial marked sector.
  long-root-central-product-has-exact-maslov-models: that models the two commuting rank-one factors; this countermodel already includes the genuinely mixed relations (2.4), (2.5), (2.6), and (2.12).
  positive-cycle-near-unitary-edges-force-trivial-holonomy: that gives an inequality once a common positive cycle exists; this exact model proves these four faces cannot force such a cycle with omega holonomy.
---

There is an explicit representation of the group defined by Kassel relations
(2.4), (2.5), (2.6), and (2.12) on `C^24` such that

```text
w_beta^4 = omega I_24.
```

It tensors a four-point permutation solution of (2.4), (2.5), and (2.12)
with a six-dimensional Weyl clock solving (2.6).  All four relator defects
are exactly zero.  Consequently no dimension-free (or dimension-dependent)
inequality can bound the marked-word HS defect by the sum of these four
relator defects.

The matrices and direct verification are in
`research/artifacts/kassel-four-cell-exact-omega-model-2026-08-21.md`.

The first cumulative extension collision for this exact packet is computed
by `kassel-27-28-charge-the-explicit-omega-packet`: either (2.7) or (2.8)
extends separately, but together they have squared defect at least `2/5`
when the four-cell generators are frozen.
