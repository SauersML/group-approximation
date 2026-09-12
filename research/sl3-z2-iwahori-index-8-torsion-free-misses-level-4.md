---
rg: 2
id: sl3-z2-iwahori-index-8-torsion-free-misses-level-4
kind: claim
title: No torsion-free index-8 subgroup of the pro-2 Iwahori of SL_3(Z_2) contains the level-4 kernel
distinct_from:
  e33-no-unique-product-pairs-of-small-radius: that is a SAT census of unique products in a Kazhdan group; this is an exhaustive linear-algebra census of 2-adic open subgroups.
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
  - experiments/strong-atiyah-sl3z/iwahori_level4_census.py
  - experiments/strong-atiyah-sl3z/iwahori_level4_census.out
---

**ESTABLISHED** by [[sl3-z2-iwahori-level-4-census-proof]].

Let `I <= SL_3(Z_2)` be the pro-2 Iwahori subgroup and
`K_j = ker(SL_3(Z_2) -> SL_3(Z/2^j))`. If `W <= I` is open of index 8 and contains
`K_2`, then `W` contains an involution.

This narrows `sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8`. It does not
refute it: subgroups containing `K_4` but not `K_2` are still unsearched.
