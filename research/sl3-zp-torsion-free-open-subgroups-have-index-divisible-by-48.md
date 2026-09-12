---
rg: 2
id: sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48
kind: claim
title: Every torsion-free open subgroup of SL_3(Z_p) has index divisible by 48, for every prime p
distinct_from:
  sl3-z2-iwahori-index-8-torsion-free-misses-level-4: that excludes only index-8 subgroups of the Iwahori containing the level-4 kernel; this excludes all of them by an exhaustive mod-16 search, and covers the odd primes.
  sl3z-strong-atiyah-denominators-divide-48: that is the rank bound obtained by restricting to congruence subgroups; this shows that restricting to subgroups with torsion-free p-adic closure cannot improve it.
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
  - experiments/strong-atiyah-sl3z/iwahori_index8_search.g
  - experiments/strong-atiyah-sl3z/iwahori_index8_search.sbatch
  - experiments/strong-atiyah-sl3z/iwahori_index8_search.out
---

**ESTABLISHED** by [[sl3-zp-torsion-free-index-48-proof]].

For every prime `p` and every torsion-free open subgroup `W <= SL_3(Z_p)`,

    48 divides [SL_3(Z_p) : W].

In particular the pro-2 Iwahori subgroup of `SL_3(Z_2)` has no torsion-free
subgroup of index 8. This refutes
`sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8`.

**Consequence for Strong Atiyah.** Let `H <= SL_3(Z)` have finite index, and
suppose its closure `H-bar` in `SL_3(Z_p)` is torsion-free for some prime `p`.
Then 48 divides `[SL_3(Z) : H]`:
- `H-bar` is open, by the congruence subgroup property;
- `SL_3(Z)` is dense in `SL_3(Z_p)`, so
  `[SL_3(Z) : SL_3(Z) cap H-bar] = [SL_3(Z_p) : H-bar]`;
- `H <= SL_3(Z) cap H-bar`.

So restricting ranks to the subgroups where Farkas--Linnell applies through a
`p`-adic closure gives at best `rk in (1/48)Z`. That is exactly
`sl3z-strong-atiyah-denominators-divide-48`. The Strong Atiyah denominator 24
for `SL_3(Z)` cannot be reached by this index method.
