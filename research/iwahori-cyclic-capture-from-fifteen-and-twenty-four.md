---
rg: 2
id: iwahori-cyclic-capture-from-fifteen-and-twenty-four
kind: route
title: Derive two power defects and round the forced cubic unipotent
target: one-almost-abelian-iwahori-vertex-has-linear-capture
requires: []
artifacts:
  - research/artifacts/one-vertex-abelian-iwahori-capture-2026-09-08.md
---

The exact modular relations make `Ad(S_2)^2` fix `T_2`. The first
commutator and the two edge errors bound
`Ad(S_2)T_2-T_2^4`; iterating this conjugacy gives the fifteenth-power
defect. Reordering three first-vertex factors gives the twelfth-power
bound for `T_1`, hence the twenty-fourth-power bound for `T_2`.
The identity `3=2*24-3*15` controls `T_2^3-I`.

The resulting second-vertex commutator bound and the same three-swap
calculation control `S_2-I`; the upper edge controls `S_1-I`.
Nearest-cube-root rounding obeys `||C-T_2||_p<=||T_2^3-I||_p/2`
for every Schatten norm at once. Exact compatibility and the displayed
generator costs follow by finite unitary telescoping. Every constant
and the rounding inequality are derived in the artifact.
