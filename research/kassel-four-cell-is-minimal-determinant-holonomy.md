---
rg: 2
id: kassel-four-cell-is-minimal-determinant-holonomy
kind: claim
title: Four mixed Kassel relators form the support-minimal determinant holonomy certificate for the long-root central word
artifacts:
  - research/artifacts/kassel-four-cell-determinant-holonomy-2026-08-21.md
distinct_from:
  c2-root-commuting-cycle-is-maslov-trivial: that rules out curvature on the commuting-root graph; this locates the first scalar holonomy certificate among noncommuting Chevalley relations.
  positive-cycle-near-unitary-edges-force-trivial-holonomy: that converts an already synchronized positive block cycle into a dimension-free HS estimate; the determinant certificate here does not construct such a positive cycle.
  long-root-central-product-has-exact-maslov-models: that gives exact matrix models on the two rank-one central product; this identifies the first four mixed faces that escape that product.
---

In the abelian/determinant shadow of Kassel's `C2` presentation, let
`r4,r5,r6,r12` denote the relator phases of (2.4), (2.5), (2.6), and
(2.12).  Then the phase `m` of the long-root word `w_beta^4` satisfies

```text
m = -8 r4 + 4 r5 + 2 r6 - 8 r12.
```

This support is minimal: after deleting any one of the four relations there
is an exact one-dimensional assignment for the other three with
`w_beta^4=exp(2 pi i/3)`.  Hence this four-face cell is the smallest scalar
mixed atlas that sees the order-three mark.

For matrices the identity forces only `det(w_beta^4)=1`, which is compatible
with `w_beta^4=omega I_d` for `3|d`; normalized determinant is not uniformly
HS-continuous.  Thus the calculation locates the noncommuting seam but does
not close the Maslov projective-defect gap.

In fact `kassel-four-cell-has-exact-omega-model` realizes this compatibility
exactly in dimension `24`.  Therefore these four faces have no marked-word
energy inequality at all; a surviving atlas must add another mixed relation
that couples the permutation and clock tensor factors of that countermodel.

The proof and explicit deleted-face assignments are in
`research/artifacts/kassel-four-cell-determinant-holonomy-2026-08-21.md`.
