---
rg: 2
id: property-tt-mod-t-rigidity-for-elementary-groups-proof
kind: route
title: Relative TT on the root subgroups, normalized and globalized, then bounded generation
target: property-tt-mod-t-rigidity-for-elementary-groups
requires: [elementary-group-property-t-over-free-algebras]
artifacts:
  - GroupApproximation/PropertyTT/PaperStatements.lean
  - GroupApproximation/PropertyTT/FiniteTypeLeavittTT.lean
  - GroupApproximation/PropertyTT/FiniteTypeRankFourRelativeTT.lean
---

## Why sufficient

The prerequisite supplies property `(T)`, which is one of the two ingredients
of the globalization step and is not otherwise available in this generality.

**Relative on a root.**  `freeCharacteristicTwo_root_hasRelativeTT` gives
relative `(TT)` for a root subgroup over a finite free characteristic-two
algebra, through the localized plane and plane-energy estimates
(`freeCharacteristicTwo_localizedPlaneEstimate`,
`freeCharacteristicTwo_planeEnergyEstimate`).

**Moving between roots.**  The row-embedding and inverse-transpose statements
(`freeCharacteristicTwo_rowEmbedding_controlRoot`,
`freeCharacteristicTwo_inverseTranspose_root`,
`freeCharacteristicTwo_rowEmbedding_elementaryRoot`) carry the estimate around
the root system, and `coordinateBlock_factorization` plus
`threeMove_diagonalPivot` are the elimination facts that make
`elementaryGroup_eq_generalLinear` available in this setting.

**Globalization.**  `kazhdan_normalizedSet_globalization` upgrades relative
`(TT)/T` on a generating set that the subgroup normalizes to relative `(TT)/T`
for the subgroup — and its hypothesis list is exactly property `(T)` of the
ambient group plus normalization, which is where the prerequisite is consumed.

**Bounded generation.**  `quasiCocycle_list_product_bound` bounds a
quasi-cocycle along a product, so a bounded-generation expression of an
arbitrary element in root elements turns the relative statements into the
global one: `finiteFreeQuotient_rankFour_hasTTmodT`, and then
`finiteFreeQuotient_elementaryGroup_hasTTmodT` at every rank at least two.

## Not a restatement

The prerequisite is a spectral-gap statement about unitary representations with
no cocycle in it; the target is about quasi-cocycles and their coboundaries,
carries division and diagonal-class hypotheses the prerequisite does not
mention, and is false for groups with `(T)` in general.
