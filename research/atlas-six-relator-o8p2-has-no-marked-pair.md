---
rg: 2
id: atlas-six-relator-o8p2-has-no-marked-pair
kind: claim
title: No marked A8 pair in O8+(2) satisfies the Atlas six-relator quotient
artifacts:
  - experiments/atlas_o8p2_six_relator_screens.py
  - experiments/atlas-six-relator-o8p2-screens.json
distinct_from:
  atlas-o8p2-ten-marked-packet-collision-screens-are-empty: that excludes the stronger sixteen-edge packet plus collision; this tests only the five saturated boundary words and centrality word c_19243.
  atlas-six-relator-hs-has-no-marked-pair: that tests the preceding Higman--Sims equality family; this exhausts all six triality A8 classes in O8+(2).
---

No pair of marked `A8` charts in `G=O8+(2)` satisfies

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                 (S6O8-1)
```

The six ambient chart classes and their marking normalizers reduce the pair
problem to the ten screens in
`atlas-o8p2-cross-class-pairs-reduce-to-ten-marked-screens`.  The exact
first-failure census after imposing `s_0` is

```text
marked pair          s_0 fiber     s_11   s_30  s_44  s_55  c_19243  survive
N1--N2 parity 0         36,864    36,864      0     0     0       0       0
N1--N2 parity 1         36,864    36,864      0     0     0       0       0
O1--O2               2,985,984 2,984,704  1,216    56     7       1       0
N1--O1 parity 0        331,776   331,776      0     0     0       0       0
N1--O1 parity 1        331,776   331,776      0     0     0       0       0
N1--O2 parity 0        331,776   331,776      0     0     0       0       0
N1--O2 parity 1        331,776   331,776      0     0     0       0       0
N1--N1 parity 0         36,864    36,864      0     0     0       0       0
N1--N1 parity 1         36,864    36,768     80    12     3       1       0
O1--O1               2,985,984 2,984,704  1,216    56     7       1       0.
                                                               (S6O8-2)
```

The diagonal screens range over every ambient conjugator, including the
same-carrier cells.  Thus `(S6O8-2)` does not rely on importing the stronger
packet exclusion on those cells.  Exactly three conjugators survive all five
boundary words—one in each `O--O` row and one in the twisted `N1--N1` row—and
`c_19243` rejects each one.

