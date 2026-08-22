---
rg: 2
id: leavitt-padded-center-template-has-no-degree2-packet
kind: claim
title: The padded central-killing template has no degree-two full-packet realization
artifacts:
  - research/leavitt-padded-center-template-degree2-proof.md
  - research/artifacts/search-postpivot-highvalence.py
  - research/artifacts/search-postpivot-cyclic-topology.py
  - research/artifacts/search-leavitt-degree2-postpivot.py
  - research/artifacts/search-leavitt-degree2-postpivot.sbatch
distinct_from:
  leavitt-direct-tail-transport-screen-is-empty: that excludes two trivalent transport gates; this screen first finds a valid abstract nine-valent central-killing relator and then excludes its shortest exact full-packet realization.
---

The abstract post-pivot incidence word with four dummy corners does reduce
exactly to `[c,d]`, and it first occurs as a cyclic-cover topology in degree two
and length ten.  Nevertheless, none of the 6,048,000 placements of the full
Leavitt coefficient packet in those shortest topologies makes the literal
Reidemeister--Schreier quotient kill `[c,d]` after the unary orbit is solved.

The next unfenced topology is degree three and length eleven, where two unary
orbits coexist with the nine-valent orbit.  The second pivot is genuine new
algebraic data and is not covered by this claim.
