---
rg: 2
id: atlas-six-relator-l5-has-no-marked-pair
kind: claim
title: Neither marked A8 parity in L5(2) has a six-relator pair
artifacts:
  - experiments/atlas_six_relator_gl5_scan.py
  - experiments/atlas-six-relator-gl5-scan.json
distinct_from:
  atlas-a4-gl5-packet-collision-screen: that uses all thirty packet words and q_19243 in the natural marking parity; this uses five saturated words and c_19243 in both marking parities.
  atlas-a4-gl5-dual-packet-collision-screen: that is the full-packet inverse-transpose screen; this evaluates the weaker literal six-relator quotient.
  atlas-a8-index-91-to-496-reaches-standard-l5: that classifies every A8 subgroup and the two marking parities; this excludes the six words in those two sectors.
---

Let `G=L_5(2)=GL_5(2)` and let

```text
H=diag(GL_4(2),1) ~= A8,      [G:H]=496.
```

No ordered pair of injective marked `A8` charts in `G` satisfies

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                 (S6L5-1)
```

Every `A8<G` is conjugate to `H`, and `N_G(H)=H`.  Hence there are two
relative marking parities: natural and inverse-transpose.  The exact census
ranges all `9999360` ambient conjugators in each parity, using the faithful
natural permutation image.  The first-failure totals are

```text
             s_0       s_11  s_30  s_44  s_55  c_19243  survivors
natural   9698304      300384   576    72     18         6          0
dual      9698304      301056     0     0      0         0          0.
                                                               (S6L5-2)
```

Thus the natural parity has six five-row survivors and the last word kills
all six, while the dual parity already dies on the first two rows.  The
calculation is exact finite permutation-group arithmetic.

This excludes the index-496 simple boundary.  It remains an exact-zero
screen and does not supply a uniform normalized-HS gap.
