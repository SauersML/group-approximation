---
rg: 2
id: atlas-six-relator-hs-has-no-marked-pair
kind: claim
title: The S8-derived A8 class in HS has no six-relator marked pair
artifacts:
  - experiments/atlas_six_relator_hs_scan.py
  - experiments/atlas-six-relator-hs-scan.json
distinct_from:
  atlas-hs-equality-escape-must-cross-s8-maximals: that uses all thirty packet rows and q_19243 to remove the identity cell; this tests the weaker five saturated rows and c_19243 on all five cells.
  atlas-six-relator-next-simple-target-is-hs: that reduces the next interval to one conjugator family; this exhausts that family.
---

Fix the derived `A8` of a maximal `S8<HS`.  No relative conjugator in `HS`
satisfies all six literal relators.

The exact `S8`--`S8` double-coset decomposition has five cells, with sizes
and intersection orders

```text
cell size       |S8 intersect S8^g|
40320                 40320
1128960                1440
4233600                 384
13547520                120
25401600                 64.                         (S6HS4)
```

The cells partition all `44352000` elements of `HS`.  Since the normalizer
is `S8` and its noninner coset induces `Out(A8)`, this single decomposition
already contains both marking parities.

The identity cell has one five-row survivor and the intersection-120 cell
has two.  In all three cases `c_19243` is nonidentity.  Every other cell has
zero five-row survivors, so the global six-word survivor count is zero.
All calculations use the official ATLAS degree-100 generators and maximal
`S8` straight-line program with exact permutation arithmetic.
