---
rg: 2
id: universal-leavitt-el4-nonsofic-proof
kind: route
title: Property (T) at ranks three and four, a non-LEF corner witness, and the compression criterion
target: universal-leavitt-el4-nonsofic
requires: [one-sided-compression-nonsofic-criterion]
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
  - GroupApproximation/Leavitt/FamilyRankFour.lean
  - GroupApproximation/Leavitt/UniversalPropertyT.lean
  - GroupApproximation/PropertyT/FiniteTypeCharacteristicTwoPropertyT.lean
---

## Why sufficient

The prerequisite is the criterion; what this route supplies is its three
inputs, each a closed declaration rather than a hypothesis, for one explicit
group.

**The criterion.**  `not_isSofic_of_not_isLEF`: a one-sided compression setup
whose ambient group and rank-three core both have property `(T)`, together with
a corner witness that is not LEF, forces the ambient group to be nonsofic.
`UniversalRankFour.compressionSetup` is the setup — the compressors are the
Leavitt words, and `compressedEnd_spec`, `centralizes` and `disjoint` are the
centralizer and disjointness calculations of the rank-four pipeline.

**Property `(T)`.**  Every finite-type `ZMod 2`-algebra is a quotient of a free
algebra on a finite type, so the kernel-checked free-algebra theorem descends to
its elementary rank-three group
(`PropertyT/FiniteTypeCharacteristicTwoPropertyT`); the explicit Leavitt rank
equivalence transfers `(T)` to rank four (`Leavitt/UniversalPropertyT`).

**The witness.**  `UniversalRankFour.witness_not_isLEF` -- the explicit non-LEF
corner.

**The transfers.**  Everything else in the claim is soficity passing along
injections and isomorphisms: `isSofic_of_injective` for `EL_4 <= GL_4`,
`isSofic_mulEquiv_iff` for the rank three/four equivalence and for
`rankSuccEquiv`, and `prefixUnitsEquiv` at the left-comb complete prefix code
for `GL_{m+1} =~ A^x`.  Infiniteness is derived rather than assumed
(`elementaryGroup_infinite`), and finite generation transports along a
surjection.
