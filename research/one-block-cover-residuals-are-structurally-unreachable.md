---
rg: 2
id: one-block-cover-residuals-are-structurally-unreachable
kind: claim
title: The one-block Hilbert-hotel cover's residual record cannot be inhabited, because the Kazhdan source maps into the model and the covering map runs the wrong way
distinct_from:
  hilbert-hotel-block-cover-is-unconditional: that claim is the positive endpoint over the TWO-block cover, whose presentation carries the corner; this claim says the one-block record it replaced is not merely unfinished but structurally closed to the obvious route.
  hilbert-hotel-model-is-unconditionally-non-mf: that is about the model itself, where no covering map appears; this is about what a Shalom cover of it can and cannot inherit.
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelCover.lean
  - GroupApproximation/Leavitt/HilbertHotelCoverDischarges.lean
  - GroupApproximation/Leavitt/HilbertHotelCoverBlock.lean
  - GroupApproximation/Leavitt/ConjProductClosure.lean
---

`HilbertHotel.Cover.CoverResiduals` has nine fields.  **Six are discharged**
and three are not:

```text
discharged: relator_vanishes, conjProduct_mem, kazhdan, defect_ne_one,
            tau_compresses, mark_commutes
open:       core, normalClosure_defect_eq_top, top_le_defectNormal
```

The three open ones are not three problems.  `top_le_defectNormal` mentions
`core.defectNormal`, so it cannot even be stated without a `core`; the two
independent obstructions are **`core`** and **`normalClosure_defect_eq_top`**,
and each is blocked by the same one-way arrow.

## `core` is blocked because the Kazhdan source is downstairs

`core : KazhdanCompressionCore Gamma (CoverGroup C)` asks for a homomorphism
from the rank-four Kazhdan corner into the *cover*.  There is none to be had:
`Gamma = E_4(R)` embeds in the model, and the only map between the two groups
is the covering surjection `CoverGroup ->> Model`, which runs the wrong way.
No identity of the model pulls back along it.

## `normalClosure_defect_eq_top` is blocked because normal closures push forward

Saturation is proved downstairs: the defect normally generates the model.  A
surjection carries that forward and no further --- for `phi : C ->> M` onto
with the defect `d`,

```text
phi(<<d>>) = <<phi d>> = M   gives   <<d>> * ker(phi) = C,
```

never `<<d>> = C`.  So the cover has to **impose** its saturation relators, one
per generator, rather than inherit them; that is what `conjProduct_mem` is for,
and it is exactly why `conjProduct_mem` is a *different statement* from the
model-level saturation and had to be proved separately.

## What this refutes

The reading that the one-block cover was six-ninths finished and needed three
more lemmas of the same kind.  It was not: the remaining fields are the ones
that require the corner to be present upstairs, and no amount of work on the
one-block presentation supplies it.  The two-block construction of
[[hilbert-hotel-block-cover-is-unconditional]] is not an optimization of this
route, it is a different group chosen so the obstruction does not arise.

## Naming trap that makes this look better than it is

Three declarations named as if they discharged the open fields do exist, and
none of them does: `Cover.top_le_defectNormal` is about `Model`,
`HilbertHotel.normalClosure_defect_eq_top` is about the elementary base, and
`CoverBlock.top_le_defectNormal` and `CoverBlock.coverCore` are about
`CoverGroup_2`, a different group whose Kazhdan source is not even `Gamma`.
Counting by name gives seven or eight of nine; counting by type gives six.
