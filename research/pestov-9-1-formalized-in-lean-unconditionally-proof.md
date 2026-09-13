---
rg: 2
id: pestov-9-1-formalized-in-lean-unconditionally-proof
kind: route
title: The Palomar Pestov 9.1 theorems follow from the witness assembly with no hypotheses
target: pestov-9-1-formalized-in-lean-unconditionally
requires: []
artifacts:
  - GroupApproximation/Pestov91/WitnessAssembly.lean
  - Palomar/Pestov91Solution.lean
  - scripts/PalomarPestov91Axioms.lean
---

Direct proof, in the development.

1. `GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef` (`WitnessAssembly.lean`) has no
   hypotheses: it applies `exists_infinite_simple_kazhdan_lef_of_witnessRing` to
   `witnessRing_isFinitelyGeneratedRing` (`WitnessRing.lean`) and `witnessRing_isLEFRing`
   (`LEFWitness.lean`), and that lemma applies `exists_infinite_simple_kazhdan_lef_of_elementary`
   (`Assembly.lean`) to `isSimpleGroup_elementaryGroup_witnessRing` (`WitnessSimple.lean`),
   `elementaryModCentre_crossedProduct_infinite` (`CentreSkew.lean`) and `isLEF_elementaryGroup`
   (`LEF.lean`), with property (T) from `elementary_hasKazhdanPropertyT` (`Kazhdan.lean`).
2. `Palomar/Pestov91Solution.lean` repeats the challenge's shared block byte for byte, bridges
   `HasKazhdanPropertyT.{0, 0}` to the challenge's `HasPropertyT` through
   `hasKazhdanPropertyT_iff_complex`, `IsLEF` to `IsSoficGroup` through `isSofic_of_isLEF`, and
   `IsSoficGroup` to `IsHyperlinearGroup` through `isHyperlinear_of_isSofic`, and proves
   `Pestov91.exists_infinite_simple_propertyT_hyperlinear` and
   `Pestov91.exists_infinite_simple_propertyT_sofic`.
3. `scripts/PalomarPestov91Axioms.lean`, run by `.github/workflows/palomar-check.yml`, checks that
   both closures are exactly `propext`, `Classical.choice`, `Quot.sound` (run 34761488911 on
   7bbaa02ac, success). The `Palomar comparator` workflow with NanoDa accepted
   `Palomar/comparator-pestov91.json` at e32bac3f3 (run 34751904895) and at 7bbaa02ac (run
   34761506719).
