---
rg: 2
id: atlas-first-nonscalar-mixed-row-same-source-proof
kind: route
title: Replay the canonical row order and evaluate the first survivor by block matrix units
target: atlas-first-nonscalar-mixed-row-is-same-source-commutation
requires: []
---

Run `experiments/atlas_first_nonscalar_mixed_row_audit.py` on MSI. The
canonical generator emits `200` one-root rows followed by `2,980` orthogonal
root rows and `1,432` multiplication rows. The literal mixed-direction and
nonconstant-coefficient filter first accepts `orth_12_32_ee` at zero-based
index `280`; replay of the sparse translated word gives `52` syllables and
`X`-length `166`.

For the mathematical check, write the two elementary nilpotent blocks as
`N=iota_1 a p_2` and `M=iota_3 b p_2`. Orthogonality of the root-index
summands gives `NM=MN=0`. In characteristic two, `1+N` and `1+M` are
involutions and commute. This construction permits arbitrary object
dimensions and is exactly the same-source special case of the Morita model
in `mixed-steinberg-loops-admit-morita-rectangular-model`. It remains valid
after substituting any finite prefix realization for the coefficient maps,
so the coherent tower satisfies this newly inspected row with zero defect.
