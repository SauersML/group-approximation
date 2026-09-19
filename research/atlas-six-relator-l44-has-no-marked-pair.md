---
rg: 2
id: atlas-six-relator-l44-has-no-marked-pair
kind: claim
title: L4(4) has no six-relator marked A8 pair in any embedding class or marking parity
artifacts:
  - experiments/atlas-l44-a8-classification.json
  - experiments/atlas-six-relator-l44-subfield-screens.json
distinct_from:
  atlas-six-relator-l44-subfield-has-no-marked-pair: that is the exact two-parity screen for the displayed subfield chart; this combines it with the complete A8 embedding classification.
  atlas-l44-has-one-a8-class-with-self-normalizer: that classifies subgroups and markings without evaluating the six relators; this imports the existing exact screen.
  atlas-l44-subfield-packet-collision-exclusion: that uses the larger twelve-edge packet and collision; this uses only the five saturated words and c_19243.
---

**ESTABLISHED.**  No two marked subgroups `A,B~=A8` generating `L4(4)` can
satisfy

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                    (S6L44A-1)
```

Indeed, `atlas-l44-has-one-a8-class-with-self-normalizer` proves there is one
subgroup class, with self-normalizer and exactly two unabsorbed relative
marking parities.  These are exactly the inner and graph cases exhaustively
enumerated by `atlas-six-relator-l44-subfield-has-no-marked-pair`.  Their
survivor counts are both zero.  No cross-class screen is needed.

