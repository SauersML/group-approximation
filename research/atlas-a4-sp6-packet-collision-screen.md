---
rg: 2
id: atlas-a4-sp6-packet-collision-screen
kind: claim
title: The orthogonal A8 class in Sp6(2) has no packet-plus-19243 realization
artifacts:
  - experiments/atlas_a4_sp6_packet_scan.py
  - experiments/atlas-a4-sp6-packet-collision-scan.json
distinct_from:
  atlas-a4-gl5-packet-collision-screen: that exhausts the GL5(F2) carrier; this tests the previously unscreened orthogonal S8-derived A8 class in Sp6(2).
  atlas-seven-word-a9-a10-exclusion: that tests alternating natural-action carriers using seven words; this uses the complete thirty-word A4 packet and collision 19243 in a symplectic carrier.
---

Let `H=A8` be the derived subgroup of an `O_6^+(2):2 ~= S8` maximal subgroup
of

```text
G=Sp_6(2),       |G|=1451520.
```

Exact GAP arithmetic finds `36` such `S8` maximal subgroups, whose derived
`A8` subgroups form one `G`-conjugacy class, with

```text
|N_G(H)|=40320.
```

Fix the first labeled chart embedding and conjugate the second by every one
of the `1451520` elements of `G`.  The normalizer contains the outer
automorphism of `A8`, so this also covers both label parities in this
orthogonal conjugacy class.  Of those conjugators, exactly `280` satisfy all
thirty A4 packet words.  None of the `280` also kills `q_19243`:

```text
packet survivors                 280
packet-plus-collision survivors    0.                    (A4-SP6-SCREEN)
```

This excludes one natural finite carrier but is not a proof that
`Gamma_A4` has no finite quotient and is not evidence by itself for a CE
obstruction.  Other conjugacy classes or other finite groups remain possible.
