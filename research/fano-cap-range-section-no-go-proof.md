---
rg: 2
id: fano-cap-range-section-no-go-proof
kind: route
title: Affinize every cap range and project the resulting affine gadget
target: fano-cap-range-sections-cannot-encode-nonaffine-relations
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

For each occurrence, the Fano criterion places its affine range hull inside
`R_*`.  The simultaneous affine replacement therefore contains the chosen
section but remains a subsystem of the original gadget.  Its visible
projection both contains and is contained in `C`, hence equals `C`.  Since
existential projection preserves affine relations, `C` must be affine.
