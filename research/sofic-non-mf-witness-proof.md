---
rg: 2
id: sofic-non-mf-witness-proof
kind: route
title: Build the sofic telescope and transport the invisible sign to it
target: sofic-non-mf-witness
requires: [literal-central-mark-corona-invisible, finite-telescope-level-coset-orbits, finite-site-orbits-invariant-clifford-kernel]
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
  - GroupApproximation/Sofic/LiteralWitnessConsequences.lean
  - GroupApproximation/Endpoint/NonMFImpact.lean
---

## Why sufficient

Every finite telescope window lies in a single level `Gamma_n`.  Finite
index of the compressing range makes `Gamma_n` commensurable with the base,
so `Gamma_n` has finite orbits on the lamp-site space.  Finite site orbits
put every finite Clifford-lamp window inside a finite
`Gamma_n`-invariant subgroup.  The local finite-kernel criterion therefore
makes `ClLamp(X) semidirect_product Telescope(alpha)` sofic.

Reassociating the iterated semidirect product exposes the remaining split
integer extension, which is sofic by the explicit cyclic-level model.  The
concrete base is sofic through its integral residually finite model, and the
doubled translation range has index at most eight, so the generic theorem
applies to `W`.  Finally, the surjection `E -> W` sends the universal
MF-invisible mark to the nontrivial Clifford sign; hence `W` is non-MF.
`NonMFImpact.witness_sofic_nonMF` packages the resulting closed statement.
