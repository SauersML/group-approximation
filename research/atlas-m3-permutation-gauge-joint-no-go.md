---
rg: 2
id: atlas-m3-permutation-gauge-joint-no-go
kind: claim
title: The first multiplicity-three permutation-gauge ansatz misses both kernel relations
artifacts:
  - experiments/atlas_a4_m3_permutation_gauge_ansatz.py
  - experiments/atlas-a4-m3-permutation-gauge-ansatz.json
distinct_from:
  atlas-multiplicity-two-joint-kernel-slice-is-empty: that exhausts all effective gauges over 1262 F4-seeded H6 lifts at multiplicity two; this tests only one universal binary seed and the 720 permutation gauges at multiplicity three.
---

The inner packet has the binary full-packet alignment

```text
U0=2841 in GL4(2).                                    (M3P1)
```

Repeat it three times.  In the coordinate `(RHG3)`, restrict the effective
`GL6(2)` gauge to the 720 permutation matrices on the six-dimensional
H6-trivial carrier.  Exactly 288 gauges retain the H18 packet.  Every one has

```text
(rank(q_19243-I),rank(q_14-I))=(3,3).                 (M3P2)
```

Thus neither relation, and hence not their joint system, has a zero in this
ansatz.  This is a bounded symbolic no-go only.  General `GL6(2)` gauges and
other H6 seed cells are not screened.
