---
rg: 2
id: finite-telescope-level-coset-orbits-proof
kind: route
title: Prove finite level orbits through commensuration of the base
target: finite-telescope-level-coset-orbits
requires: []
artifacts:
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
---

## Why sufficient

Successive telescope levels have relative index equal to the index of
`alpha.range`; hence every level is commensurable with level zero.  After
embedding the telescope in the vertical semidirect product, the stable
letter conjugates the base to the compressed range, which is again
commensurable with the base.  The level-zero copy and stable letter generate
the vertical group, so the entire vertical group commensurates the base.

For a level `L` acting on `V/B`, the stabilizer of the coset represented by
`g` is the pullback to `L` of `gBg^-1`.  Commensurability gives this
stabilizer finite index in `L`; orbit--stabilizer therefore makes the orbit
finite.  `MappingTelescopeFiniteOrbits.lean` checks every step, including
the stabilizer identity and the relative-index calculation.
