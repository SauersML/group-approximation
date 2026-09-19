---
rg: 2
id: leavitt-d4-l14-fifteen-winner-profile-proof
kind: route
title: Rank and expose the five fifteen-winner carrier classes
target: leavitt-d4-l14-fifteen-winner-profile-has-five-classes
requires:
  - leavitt-d4-l14-three-winner-boundary-needs-21-blocks
---

Run the ranker with

```text
--length 14 --profile=---+-+++++-+++ --balanced-only
--show-rank 9 --classify-rank 9.
```

It returns fifteen winners and the cyclic classes

```text
N(0;115), N(0;214),
I(0;124), I(1;115), I(4;115),
```

each with multiplicity three.  The exact pivot and residual corners are

```text
H=g9_0g10_1g11_0g12_1g13_2g0_3g1_2g2_1g3_0
  g4_1g5_0g6_1g7_2g8_3;

A0=g1_3g2_2g3_1g4_2g5_1g6_2g7_3;
B0=g8_0g9_1g10_2g11_1g12_2g13_3; C0=g0_0;

A1=g2_3g3_2g4_3g5_2g6_3;
B1=g7_0g8_1g9_2g10_3g11_2g12_3;
C1=g13_0g0_1g1_0;

E1=g3_3; E2=g4_0; E3=g5_3;
E4=g6_0g7_1g8_2g9_3; E5=g10_0; E6=g11_3;
E7=g12_0g13_1g0_2g1_1g2_0.
```

Unlike the preceding profiles, the common trivalent carrier compares the
singleton `C0` with the five-syllable `A1`, so it does not collapse two slots
immediately.  The correct next step is automatic target matching followed by
the all-maximal forest/state-semiring pipeline, separately for the five
listed classes.
