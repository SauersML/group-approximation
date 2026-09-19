---
rg: 2
id: ct-p-z-positive-ray-torsion-and-finiteness-are-decidable-proof
kind: route
title: "Explicit constants of ray-cocycle pumping give a computable finite permutation model, hence computable order and group-size bounds, hence algorithms via the decidable word problem"
target: ct-p-z-positive-ray-torsion-and-finiteness-are-decidable
requires:
  - periodic-k-graph-subgroups-with-ray-cocycle-are-finite
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The body of
`ct-p-z-positive-ray-torsion-and-finiteness-are-decidable` makes explicit the constants that
`periodic-k-graph-subgroups-with-ray-cocycle-are-finite` (bh-kourovka) already defines:
`D`, `K`, `E`, `C = m_E`, `B = KC` and `n`. It reads off `|F_n| ≤ N(S)`, and it combines that
bound with the decidable word problem of `CT(Z)`.
