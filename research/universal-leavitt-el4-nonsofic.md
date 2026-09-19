---
rg: 2
id: universal-leavitt-el4-nonsofic
kind: claim
title: The rank-four elementary group over the universal binary Leavitt algebra is nonsofic, with property (T)
distinct_from:
  openai-leavitt-unit-nonsofic: That is the first nonsofic group, reached through a nine-leaf configuration with Thompson's `V` as the non-LEF witness; this is this repository's own kernel-checked theorem over the same algebra -- `BinaryLeavittAlgebra (ZMod 2)` IS `L_(F_2)(1,2)` -- at rank four, with a two-relator witness and proved property (T). The two proofs are independent, and this one does not depend on that one; it is one of that node's two routes.
  literal-group-not-sofic: That claim denies soficity of the manuscript's non-MF group E, which is a different group and a different mechanism; this is the one-sided-compression Kazhdan mechanism over a Leavitt algebra.
  wreath-not-sofic: That is the wreath candidate of the Kun-Thom lane; this is the elementary group of a Leavitt algebra, and the two mechanisms share only the words "not sofic".
  kun-thom-nonsofic-wreath: That is an external theorem about generalized wreath products over infranormal Kazhdan pairs, imported as established; this is about elementary groups over a Leavitt algebra. The two share the Kun and Kun-Thom inputs, which the development formalizes, but neither statement implies the other.
  nonsofic-hyperbolic-group: That asks for a nonsofic HYPERBOLIC group, a second and independent mechanism that nothing here supplies; this group is not hyperbolic and is not claimed to be.
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
  - GroupApproximation/Leavitt/FamilyRankFour.lean
  - GroupApproximation/Leavitt/UniversalPropertyT.lean
---

ESTABLISHED, unconditionally and kernel-checked.  `Endpoint/MainResults`:

* `universalLeavittEL4_not_isSofic` -- `EL_4` of the universal binary Leavitt
  algebra over `F_2` is not sofic;
* `ambient_full_profile` -- that same group is countable, finitely generated,
  infinite, has Kazhdan's property `(T)`, and is not sofic;
* `universalLeavitt_profile m` -- the same four properties for
  `EL_{m+1}` at every `m >= 1`, the rank-four theorem of the `PropertyTT/`
  development strengthened to every positive elementary rank;
* `universalLeavittEL3_not_isSofic`, `universalLeavittUnits_not_isSofic` and
  `universalLeavittGL_not_isSofic m` -- the rank-three core, the full unit
  group, and every positive-rank general linear group over the same algebra,
  each by an explicit isomorphism (the rank three/four Leavitt equivalence, and
  the complete prefix code identifying `GL_{m+1}` with the unit group).

## The mechanism, and whose theorems it runs on

`not_isSofic_of_not_isLEF` applied to the rank-four compression setup: property
`(T)` for the ambient group and for its rank-three core, plus an explicit
non-LEF corner witness.  Property `(T)` is not assumed -- it comes from the
free-algebra theorem over `ZMod 2` descending to finite-type algebras
(`PropertyT/FiniteTypeCharacteristicTwoPropertyT`), transported to rank four by
the Leavitt rank equivalence (`Leavitt/UniversalPropertyT`).

**The criterion is built on Kun and on Kun--Thom, and the development formalizes
both.**  `Criterion/CriterionAssembly` decomposes the sofic approximation into
uniform expanders with `Kun/KunFixedDecomposition.expanderDecomposition` --
Kun's expander decomposition for property-`(T)` groups (arXiv:1606.04471, 2016)
-- and `Criterion/SelectionOutput` feeds the post-selection data into
`KunThom/KunThomEssential`, the Kun--Thom expander-centralizer obstruction
(arXiv:1901.03963, 2019).  Both are proved in this repository rather than
quoted: the `LITERATURE_INPUT` roster of `scripts/Audit.lean` is empty, so no
premise in the chain is a transcription.  What is *added* on top of them is the
selection step -- passing from Kun's union of expanders to a single expanding
component on which the Kun--Thom hypothesis holds -- and that step is the only
part of the mechanism that is not one of their theorems.

## Universal versus presented

The algebra is the universal binary Leavitt algebra *constructed in the
development*, not a presented `L_k(1,2)` taken from elsewhere; the difference
matters when comparing statements with the literature, and the development is
explicit about which object each theorem is about.
