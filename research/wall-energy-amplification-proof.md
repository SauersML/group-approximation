---
rg: 2
id: wall-energy-amplification-proof
kind: route
title: Diagonal tensor powers multiply the wall overlap
target: wall-energy-amplification
requires: []
artifacts:
  - notes/TRUE_WALL_ENERGY_AND_COMMUTANT_DENSITY.md
---

Complete written argument in the artifact.  With `w=pi(h)v pi(h)^*` and
`c=tau(v^* w)`, the amplified overlap is `c^k`, so the squared energy is
`2-2 Re c^k`.  A unitary with `|tau|=1` is a scalar, so `c!=1`; if `|c|<1`
the energies tend to `2`, and if `|c|=1` the closure of `{c^k}` contains a
point of real part at most `-1/2`.  Connes embeddability and membership in
the relative commutant are preserved by finite diagonal tensor powers.
