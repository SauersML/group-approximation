---
rg: 2
id: elementary-group-property-t-over-free-algebras-proof
kind: route
title: A two-root moving-mass bound, made finite, then descended to quotients
target: elementary-group-property-t-over-free-algebras
requires: []
artifacts:
  - GroupApproximation/PropertyT/FiniteFieldElementaryPropertyT.lean
  - GroupApproximation/PropertyT/A2MagicEnergy.lean
  - GroupApproximation/PropertyT/A2MagicLaplacian.lean
  - GroupApproximation/PropertyT/FreeRootPlaneFourier.lean
  - GroupApproximation/PropertyT/ClassTwoNormalForm.lean
  - GroupApproximation/PropertyT/FiniteTypeCharacteristicTwoPropertyT.lean
---

## Direct proof, machine-checked

**The A2 mechanism.**  `A2System`, `A2MagicGraph`, `A2MagicLaplacian` and
`A2MagicEnergy` set up the six elementary roots of rank three as an `A2` root
system and bound the energy of an almost-invariant vector against the graph
Laplacian of the magic graph; `A2Kazhdan` turns that bound into a relative
Kazhdan constant for each root subgroup.

**Class two.**  The root subgroups generate a class-two nilpotent picture
rather than an abelian one, so `ClassTwoNormalForm`,
`ClassTwoApproximation`, `ClassTwoOrthogonality` and their finite counterparts
(`FiniteClassTwoOrthogonality`, `FiniteClassTwoDecompositionBound`) supply the
orthogonality and decomposition bounds the averaging needs.

**Moving mass.**  `FreeRootPlane`, `FreeRootPlaneFourier`, `FreeRootPlaneMass`
and `FreeRootCharacterValuation` bound how much mass a character can keep on a
root plane over a free algebra — this is where the coefficient field's
finiteness enters, through the character sums.

**Making it finite.**  `controlSet_isKazhdanPair` turns the limiting bound into
an explicit finite control set: every scalar multiple of the unit and every
free generator, in each of the six roots.  `freeElementary_hasKazhdanPropertyT`
is the resulting `(T)`.

**Descent.**  A finite-type `ZMod 2`-algebra is a quotient of a free algebra on
a finite type, and property `(T)` passes to quotients, which is
`FiniteTypeCharacteristicTwoPropertyT`.
