---
rg: 2
id: sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic
kind: claim
title: If SL_3(Z) is coherent, its virtually RFRS subgroups of dimension two are virtually free-by-cyclic with vanishing second L-two Betti number
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part2.md
---

Suppose `SL_3(Z)` is coherent. Let `H <= SL_3(Z)` be finitely generated and
virtually RFRS, with `cd_Q(H) <= 2`. Then `H` is virtually free-by-cyclic and
`b_2^(2)(H) = 0`.

Contrapositive, as an incoherence target: a finitely presented virtually
RFRS subgroup `H <= SL_3(Z)` with `cd_Q(H) <= 2` and Euler characteristic
`χ(H) > 0` makes `SL_3(Z)` incoherent. In dimension two,
`b_2^(2)(H) = χ(H) + b_1^(2)(H) >= χ(H)` for infinite `H`.

By `non-zariski-dense-subgroups-of-sl3z-are-coherent`, such an `H` would be a
Zariski-dense thin subgroup.
