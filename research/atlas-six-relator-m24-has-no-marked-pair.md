---
rg: 2
id: atlas-six-relator-m24-has-no-marked-pair
kind: claim
title: No marked A8 pair in M24 satisfies the Atlas six-relator quotient
artifacts:
  - experiments/atlas_m24_six_relator_screens.py
  - experiments/atlas-six-relator-m24-screens.json
distinct_from:
  atlas-m24-marked-packet-collision-exclusion: that asks for the larger packet-plus-collision system and was left open on cross fibers; this exhausts the weaker six-word system directly.
  atlas-six-relator-a12-has-no-marked-pair: that screens a normalizer which absorbs the outer marking; the self-normalizing M24 chart requires two separate marked parities.
---

The unique `A8` class in `M24` is self-normalizing and has trivial
centralizer, so there are exactly two relative marking parities.  Neither
admits

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                 (S6M24-1)
```

For each parity the exact `s_0` partition has `28` class hits, centralizer
order `21504`, and therefore `602112` seed conjugators.  The complete
first-failure census is

```text
marking    s_11    s_30   s_44   s_55   c_19243   survive
inner     601920    176     12      2        2          0
graph     602096     16      0      0        0          0.   (S6M24-2)
```

Thus the graph parity dies before the interior word, while the two inner
candidates satisfying all five boundary words are both rejected by
`c_19243`.  The two exact seed-fiber scans cover every ambient conjugator and
use no sampling or floating point.

