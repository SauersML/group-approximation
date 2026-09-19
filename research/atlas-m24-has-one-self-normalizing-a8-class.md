---
rg: 2
id: atlas-m24-has-one-self-normalizing-a8-class
kind: claim
title: M24 has one A8 class, self-normalizing with orbit type 1+8+15
artifacts:
  - experiments/atlas_m24_affine_a8_fusion.py
  - experiments/atlas-m24-affine-a8-fusion.json
distinct_from:
  atlas-m24-a8-three-carrier-fork: that only leaves three possible maximal carrier sources; this fuses the real sources and removes the duad source entirely.
  atlas-a4-m23-packet-double-coset-screen: that classifies packet survivors inside one M23 carrier; this determines the ambient M24 subgroup class and normalizer.
---

The group `M24` has exactly one conjugacy class of subgroups `A~=A8`.  In its
natural degree-24 action every such subgroup has orbit decomposition

```text
1 + 8 + 15.                                          (M24F-1)
```

Moreover

```text
N_M24(A)=A,       C_M24(A)=1,       |A^M24|=12144.   (M24F-2)
```

Fix the canonical MOG octad

```text
{3,5,6,9,15,19,23,24}.
```

Its setwise stabilizer is `V:A8` with `V~=2^4`.  There is exactly one carrier
conjugacy class of complements to `V`; exact permutation arithmetic gives
`(M24F-1)--(M24F-2)` for its representative.  The unique fixed point and
unique eight-point orbit also give a conceptual normalizer check: every
ambient normalizer preserves both, hence lies back in the octad carrier,
where the complement is self-normalizing.

