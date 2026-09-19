---
rg: 2
id: leavitt-d4-l14-three-winner-profile-proof
kind: route
title: Rank and compile the unique three-winner carrier system
target: leavitt-d4-l14-three-winner-profile-has-one-class
requires:
  - leavitt-d4-l14-n0511-is-fenced
---

Run the ranker with

```text
--length 14 --profile=---++-+++++-++ --balanced-only
--show-rank 9 --classify-rank 9
```

It returns three embeddings and one cyclic class, normal start zero with
arc sizes `(3,1,3)`.  The pivot and corners are

```text
H=g9_0g10_1g11_2g12_1g13_2g0_3g1_2g2_1g3_0g4_1g5_2g6_1g7_2g8_3;
A0=g1_3g2_2g3_1g4_2g5_3g6_2g7_3;
B0=g8_0g9_1g10_2g11_3g12_2g13_3; C0=g0_0;
A1=g3_3;
B1=g4_0g5_1g6_0g7_1g8_2g9_3;
C1=g10_0g11_1g12_0g13_1g0_2g1_1g2_0;
E1=g2_3g3_2g4_3; E2=g5_0; E3=g6_3;
E4=g7_0g8_1g9_2g10_3; E5=g11_0; E6=g12_3;
E7=g13_0g0_1g1_0.
```

Writing the seven signed atoms as `Tj=H^{-sign_j}Ej`, the winning grouping
is `T0T1T2`, `T3`, `T4T5T6`.  Literal target matching gives

```text
H A0=E7^-1 H E6^-1 H^-1 E5^-1 H;
H^-1 C0=A1^-1 H^-1;
H^-1 C1=E3^-1 H^-1 E2^-1 H E1^-1 H^-1;
K=H^-1 B0 H^-1 B1 H^-1 E4.
```

The middle equation compares `g0_0` with `g3_3` through the same carrier,
so free-product normal form forces `g0=g3=1`.  These formulas are the sole
nonabelian elimination target for the profile.
