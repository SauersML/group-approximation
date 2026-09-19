---
rg: 2
id: sofic-non-mf-witness
kind: claim
title: Six-generated sofic group that is not MF
distinct_from:
  hyperlinear-nonsofic-group: This established claim has a sofic non-MF witness; the open Pestov claim asks for a hyperlinear group that is not sofic.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralWitnessConsequences.lean
  - GroupApproximation/Sofic/SoficTelescope.lean
  - GroupApproximation/Sofic/SoficInvariantFiniteKernel.lean
  - GroupApproximation/Sofic/FiniteOrbitInvariantKernel.lean
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
  - GroupApproximation/Sofic/SoficMarkedCompression.lean
  - GroupApproximation/Sofic/LiteralBaseDoublingIndex.lean
  - GroupApproximation/Monsters/ExplicitIntegralLinearModel.lean
  - GroupApproximation/Sofic/SoficIntegerExtension.lean
  - GroupApproximation/Endpoint/NonMFImpact.lean
---

The concrete Clifford witness
`W = ClLamp(X) semidirect_product V` is finitely generated, sofic, and not
MF.  This is the premise-free Lean theorem
`GroupApproximation.NonMFImpact.witness_sofic_nonMF`.
