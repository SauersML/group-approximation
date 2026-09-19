---
rg: 2
id: one-block-cover-residuals-are-structurally-unreachable-proof
kind: route
title: Count the fields by type, then read the direction of the only available arrow
target: one-block-cover-residuals-are-structurally-unreachable
requires: []
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelCover.lean
  - GroupApproximation/Leavitt/HilbertHotelCoverBlock.lean
---

## The count

Six discharges exist and typecheck against the field they name:
`Cover.relator_vanishes` and `Cover.coverGroup_hasKazhdanPropertyT` and
`Cover.coverDefect_ne_one` in `HilbertHotelCoverDischarges`,
`Cover.conjProduct_mem_normalClosure` in `ConjProductClosure`, and
`Cover.tau_compresses` and `Cover.mark_commutes` in `HilbertHotelModelNonMF`.
For `core`, `normalClosure_defect_eq_top` and `top_le_defectNormal` at
`CoverGroup C` there is no declaration of the right type anywhere in the tree.

## The obstruction, stated as a fact about the diagram

The construction fixes a surjection `p : CoverGroup C ->> Model` and an
embedding `iota : Gamma -> Model`.  A `KazhdanCompressionCore Gamma (CoverGroup C)`
needs `Gamma -> CoverGroup C`.  Composing what exists gives only
`Gamma -> Model`, and `p` cannot be inverted: it has a kernel by construction,
since the cover is the presented group and the model is its image.  So the
field is not reachable by transport, and the file records this in its own
header as a structural rather than technical gap.

For saturation the same arrow is the obstruction in the other direction.
Normal closure is a covariant operation: `p(<<d>>) = <<p d>>`.  From
`<<p d>> = Model` one recovers `<<d>> * ker p = CoverGroup C`, and the kernel
is exactly what the covering map forgets.  The equality `<<d>> = CoverGroup C`
is strictly stronger and is not a consequence.

## Why this is a claim and not a lament

Because it is what selects the construction.  The two-block cover puts the
corner generators into the presentation, so `Gamma -> CoverGroup_2` exists by
definition and `coverCore` is buildable; and its saturation relators are
imposed rather than inherited, which is exactly the move this claim says is
forced.  The positive endpoint is
[[hilbert-hotel-block-cover-is-unconditional]], and it does not discharge a
single one-block field.
