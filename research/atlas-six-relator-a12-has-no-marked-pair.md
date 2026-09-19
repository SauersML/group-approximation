---
rg: 2
id: atlas-six-relator-a12-has-no-marked-pair
kind: claim
title: No marked natural A8 pair in A12 satisfies the Atlas six-relator quotient
artifacts:
  - experiments/atlas_a12_six_relator_screen.py
  - experiments/atlas-six-relator-a12-screen.json
distinct_from:
  atlas-natural-a8-supports-collapse-before-collision: that uses the full cross-A4 packet; this excludes the weaker five-boundary-plus-centrality system by exhaustive exact multiplication.
  atlas-six-relator-o8m2-has-no-marked-pair: that screens the preceding orthogonal endpoint; this treats the next natural alternating endpoint.
---

Every `A8<A12` acts as `8+1+1+1+1`.  For every pair of marked such charts,

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1                 (S6A12-1)
```

is impossible.  The chart normalizer and centralizer have orders `483840`
and `12`, so their quotient realizes all `40320` automorphisms of `A8`; one
ambient conjugator screen covers both relative markings.

The exact `s_0` seed has six conjugacy-class hits and `4608` conjugators per
hit, hence `27648` candidates.  Their first-failure census is

```text
s_11      s_30      s_44      s_55      c_19243      survive
27504       96        24        12          12            0.  (S6A12-2)
```

In particular twelve conjugators reach the interior word and all twelve are
rejected.  The attached script uses only exact permutation multiplication
and the same complete conjugacy-class/centralizer fiber partition as the
orthogonal screens.

