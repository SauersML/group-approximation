---
rg: 2
id: cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity
kind: claim
title: Cartan uniqueness for LC(X,F_2)⋊Z holds iff every Cartan model has a fibre-bijective Z-cocycle and the ring determines X among subshifts up to flip
distinct_from:
  subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity: that proves the equivalence with groupoid-model rigidity; this splits that rigidity into an orientation condition on models and ring rigidity among subshifts
---
**Statement.** Let X be an infinite minimal subshift and R_X = LC(X,F_2) ⋊ Z. The following are equivalent.
- (U) Every algebraic Cartan subalgebra of R_X is β(D_X) for a ring automorphism β of R_X. This is the open claim
  `subshift-crossed-product-algebraic-cartans-are-conjugate`.
- (D1) and (D2):
  - (D1) for every algebraic Cartan subalgebra B, its groupoid model G_B carries a continuous homomorphism G_B → Z that
    is bijective on every source fibre;
  - (D2) every infinite minimal subshift Y with R_Y ≅ R_X as rings is flip conjugate to X.

**Reading.** (D2) is ring rigidity among subshifts. (D1) is an orientation condition on models: a model with finite
nontrivial isotropy, or with two-ended orbits admitting no continuous orientation, fails it. The dihedral Sturmian
groupoid (artifact §5) is effective and minimal with Z/2 isotropy, so it fails (D1). Whether its Steinberg algebra is
isomorphic to some R_Y is open and would decide (U) at that Y.

Proof route: `cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS (§5); conditional on Theorem C of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`.
