---
rg: 2
id: leavitt-d4-length12-balanced-rank9-two-classes-proof
kind: route
title: Derive the two exact carrier systems and coefficient boundaries
target: leavitt-d4-length12-balanced-rank9-two-classes
requires:
  - leavitt-triangle-carrier-chirality-criterion
---

Write the two three-valent residuals as factor triples

```text
(H Ai, H^-1 Bi, H^-1 Ci),  i=0,1,
```

and the five signed atoms as

```text
T0=H E1, T1=H^-1 E2, T2=H E3,
T3=H^-1 E4, T4=H^-1 E5.
```

The raw corners for `---+-+++++++` are

```text
H =g9_0 g10_1 g11_2 g0_3 g1_2 g2_1 g3_0
   g4_1 g5_0 g6_1 g7_2 g8_3,
A0=g1_3g2_2g3_1g4_2g5_1g6_2g7_3,
B0=g8_0g9_1g10_2g11_3,       C0=g0_0,
A1=g2_3g3_2g4_3g5_2g6_3,
B1=g7_0g8_1g9_2g10_3,        C1=g11_0g0_1g1_0,
E1=g3_3, E2=g4_0, E3=g5_3,
E4=g6_0g7_1g8_2g9_3,
E5=g10_0g11_1g0_2g1_1g2_0.
```

Both classes use canonical first faces `P A Q` and `Q^-1 B R`.

For class `(1,3,1)`, cyclically assign

```text
T1=R^-1,       T2 T3 T4=C,       T0=P^-1.
```

The exact carrier equations and coefficient-only boundary are

```text
H A0=E1^-1 H^-1,
H^-1 C0=A1^-1 H^-1,
H^-1 C1=E2^-1 H,
K=H^-1B0 H^-1B1 H E3 H^-1E4 H^-1E5.             (A)
```

For class `(2,2,1)`, assign

```text
T3 T4=R^-1,       T0 T1=C,       T2=P^-1.
```

This gives

```text
H A0=E3^-1 H^-1,
H^-1 C0=A1^-1 H^-1,
H^-1 C1=E5^-1 H E4^-1 H,
K=H^-1B0 H^-1B1 H E1 H^-1E2.                    (B)
```

The common middle equation forces `g0=1` by free-factor malnormality and
`A1=1`.  The latter has exactly two branches:

```text
I:  g3=g5=1,  g2 g4 g6=1;
II: g4=1,     g3 g5=1,  g2 g6=1.
```

Thus (A) and (B), each with these two exhaustive branches, are the complete
nonabelian elimination targets at rank nine.

