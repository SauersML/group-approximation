---
rg: 2
id: jacobson-opposite-root-steinberg-closure-proof
kind: route
title: Transport both root directions through the full boundary packet and verify the six-coordinate Steinberg relations
target: jacobson-full-boundary-forces-six-coordinate-packet
requires:
  - jacobson-boundary-cell-reconstructs-finite-root-packet
  - jacobson-mixed-cells-reconstruct-full-first-level-root-packet
artifacts:
  - research/artifacts/jacobson-full-boundary-opposite-roots-and-gl6-packet-2026-09-08.md
---

The full boundary packet gives `[h x_12,Q h,x_31,P]=1`.
The split TS relation turns this into the second missing tail
stabilizer commutation. The first braid and boundary identities then
provide both stabilizers of the opposite rank-one root. Transporting
the two addition laws reconstructs the opposite additive matrix group.

The two pairing values classify all forward/opposite root pairs under
`F`. Each class has a representative inside the known five-coordinate
boundary group. Its commutator calculations give the head roots and
the local tail roots. Their natural actions on both matrix root groups
follow from those local calculations, except for the annihilator cases,
where a spare head vector or covector makes both commutator factors
commute with the tested root. These actions supply the tail addition
laws and all six-coordinate Steinberg relations.

The finite-field Steinberg presentation theorem cited in the artifact
makes the resulting group a quotient of `GL_6(F_2)`. Its literal
image is the full six-coordinate group, proving injectivity. Removing
the local tail action from the original tail gives a commuting residual
copy of `GL_3(F_2)`, distinguished by its action at higher levels.
