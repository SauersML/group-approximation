---
rg: 2
id: maximal-kazhdan-radicals-recover-scaling-lamps
kind: claim
title: Maximal Kazhdan finite radicals intrinsically recover every scaling lamp kernel
distinct_from:
  scaling-lamp-kernel-isomorphism-invariant: that is the cross-family invariance consequence; this gives the exact internal characteristic formula that proves it.
  prime-scaling-maximal-kazhdan-blocks: at prime scales an entire block stabilizer is Kazhdan and its finite radical records the prime; at composite scales the block is infinite and the recovery uses all maximal clique stabilizers.
artifacts:
  - research/artifacts/composite-scaling-kazhdan-radical-reconstruction-2026-08-30.md
---

For `m>=2`, let `N_m=<<c_m>>` be the scaling-family lamp kernel.  For an
abstract group `G`, define

```text
K_T(G)=< FinRad(H) |
          H<=G is maximal among property-(T) subgroups >.
```

For `G=E_m`, every displayed finite radical exists and

```text
K_T(E_m)=N_m.                                           (KR)
```

Thus the lamp kernel is characterized without its marked generator,
retraction, height map, or presentation.

DERIVATION
[[maximal-kazhdan-radicals-recover-scaling-lamps-proof]]
