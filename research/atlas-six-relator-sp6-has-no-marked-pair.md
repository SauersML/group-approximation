---
rg: 2
id: atlas-six-relator-sp6-has-no-marked-pair
kind: claim
title: The unique A8 class in Sp6(2) has no six-relator marked pair
artifacts:
  - experiments/atlas_six_relator_sp6_scan.py
  - experiments/atlas-six-relator-sp6-scan.json
distinct_from:
  atlas-a4-sp6-packet-collision-screen: that tests all thirty cross-A4 packet words followed by q_19243; this tests the weaker and different five saturated words followed by c_19243.
  atlas-six-relator-has-no-a11-target: that screens the natural alternating carrier through degree eleven; this screens the unique orthogonal A8 class in the nonalternating simple group Sp6(2).
  atlas-a8-index-33-to-89-is-orthogonal-sp6: that classifies the ambient A8 subgroups; this evaluates the six literal marked words on every ordered marked pair in that class.
---

Let

```text
G=Sp_6(2),        |G|=1451520,
```

and let `H~=A8` be the derived subgroup of an orthogonal maximal
`O_6^+(2):2 ~= S8`.  There are no injective marked maps

```text
i_1,i_2:A8 -> G
```

whose images satisfy all six words

```text
s_0, s_11, s_30, s_44, s_55, c_19243.                (S6SP1)
```

The exact census fixes the first marked chart and ranges the relative
conjugator over every element of `G`.  The `36` maximal `S8` subgroups have
derived subgroups in one `G`-conjugacy class, and

```text
|N_G(H)|=40320.
```

Since `N_G(H)/H` has order two, this range includes both inner and outer
markings of the second `A8` chart.  It therefore exhausts all ordered marked
pairs up to simultaneous conjugacy.

The first-failure census is

```text
word          first failures
s_0                 1410048
s_11                  41376
s_30                     80
s_44                     12
s_55                      3
c_19243                   1
survivors                  0.                         (S6SP2)
```

The counts sum to `|G|`.  In particular the five boundary words leave one
relative conjugator, and `c_19243` kills that last alignment.  All arithmetic
is exact GAP group arithmetic; no floating-point or character-value
tolerance enters the test.

This excludes the sole finite-simple carrier in the index interval
`33 <= [G:A8] < 90`.  It does not exclude larger finite simple overgroups and
does not by itself establish a dimension-uniform normalized-HS gap.
