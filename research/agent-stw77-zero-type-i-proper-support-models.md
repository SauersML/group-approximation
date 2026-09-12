---
rg: 2
id: agent-stw77-zero-type-i-proper-support-models
kind: claim
title: Zero-color maps into type-I von Neumann algebras admit proper-support models
distinct_from:
  stw77-type-i-von-neumann-targets-solve-map: that proves O-infinity-stability without a dimension hypothesis; this proves the stronger finite-dimensional model-selection statement when the map has nuclear dimension zero.
  stw77-zero-models-admit-proper-block-clustering: that asks for the selection in an arbitrary C-star target; this establishes its singleton-cluster conclusion for type-I von Neumann targets.
---

Let `A` be separable and unital, let `M` be a type-I von Neumann algebra
with separable predual, and let

```text
phi:A->M
```

be a unital nuclear-dimension-zero homomorphism.  Suppose every nonzero
positive element of `phi(A)` is properly infinite in `M`.  For every finite
`F subset A` and every `epsilon>0`, there is a unital finite-dimensional
subalgebra

```text
E=direct_sum_j E_j subset M
```

such that

```text
max_(a in F) dist(phi(a),E)<epsilon
```

and every minimal projection in every nonzero simple summand of `E` is
properly infinite in `M`.

Consequently the conclusion of
`stw77-zero-models-admit-proper-block-clustering` holds for this target
class: take singleton clusters.  Thus the measurable type-I absorption
mechanism can be made to repair the supports of the one-sided zero-color
models, not merely to produce central isometries by a separate argument.
