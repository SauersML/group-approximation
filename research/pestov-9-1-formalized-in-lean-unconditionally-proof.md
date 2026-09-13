---
rg: 2
id: pestov-9-1-formalized-in-lean-unconditionally-proof
kind: route
title: The Palomar Pestov 9.1 theorems follow from the witness assembly with no hypotheses
target: pestov-9-1-formalized-in-lean-unconditionally
requires: []
artifacts:
  - GroupApproximation/Pestov91/WitnessAssembly.lean
  - GroupApproximation/Pestov91/Assembly.lean
  - Palomar/Pestov91Solution.lean
  - scripts/PalomarPestov91Axioms.lean
---

Direct proof, in the development.

1. `GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef` (`WitnessAssembly.lean`, landed at
   5f9c16b7b) has no hypotheses: it applies `exists_infinite_simple_kazhdan_lef_of_witnessRing` to
   `witnessRing_isFinitelyGeneratedRing` (`WitnessRing.lean`) and `witnessRing_isLEFRing`
   (`LEFWitness.lean`), and that lemma applies `exists_infinite_simple_kazhdan_lef_of_elementary`
   (`Assembly.lean`) to `isSimpleGroup_elementaryGroup_witnessRing` (`WitnessSimple.lean`),
   `elementaryModCentre_crossedProduct_infinite` (`CentreSkew.lean`) and `isLEF_elementaryGroup`
   (`LEF.lean`), with property (T) from `elementary_hasKazhdanPropertyT` (`Kazhdan.lean`).
2. `Palomar/Pestov91Solution.lean` repeats the challenge's shared block byte for byte, bridges
   `HasKazhdanPropertyT.{0, 0}` to the challenge's `HasPropertyT` through
   `hasKazhdanPropertyT_iff_complex`, `IsLEF` to `IsSoficGroup` through `isSofic_of_isLEF`, and
   `IsSoficGroup` to `IsHyperlinearGroup` through `isHyperlinear_of_isSofic`. It then proves the two
   binder-free theorems `Pestov91.exists_infinite_simple_propertyT_hyperlinear` and
   `Pestov91.exists_infinite_simple_propertyT_sofic` by applying `exists_infinite_simple_propertyT_hyperlinear_of`
   and `exists_infinite_simple_propertyT_sofic_of` to `GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef`.
3. `scripts/PalomarPestov91Axioms.lean`, run by `.github/workflows/palomar-check.yml`, prints the axiom
   closure of both theorems and fails unless it lies inside `propext`, `Classical.choice`, `Quot.sound`.
   Runs 34762687202 (be41521bf) and 34765520365 (174e3006d), both successful, print
   `axiom closure (3): [propext, Classical.choice, Quot.sound]` for each theorem, with the types
   `∃ G x, Infinite G ∧ IsSimpleGroup G ∧ Pestov91.HasPropertyT G ∧ Pestov91.IsHyperlinearGroup G` and
   `∃ G x, Infinite G ∧ IsSimpleGroup G ∧ Pestov91.HasPropertyT G ∧ Pestov91.IsSoficGroup G`.
4. The `Palomar comparator` workflow with NanoDa accepted `Palomar/comparator-pestov91.json` at e32bac3f3
   (run 34751904895), at 7bbaa02ac (run 34761506719), and at 174e3006d (run 34765532993, the latest passing
   run confirmed with `gh run list` on 2026-09-13).
