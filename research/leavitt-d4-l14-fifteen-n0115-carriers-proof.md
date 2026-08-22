---
rg: 2
id: leavitt-d4-l14-fifteen-n0115-carriers-proof
kind: route
title: Compile and retract the normal fifteen-winner 0;115 system
target: leavitt-d4-l14-fifteen-n0115-carriers-are-explicit
requires:
  - leavitt-d4-l14-fifteen-winner-profile-has-five-classes
---

Use the first normal rank-nine embedding.  With the raw corners recorded in
the profile classification, its target matching is

```text
T0=id0^-1, T1=id4^-1, T2 T3 T4 T5 T6=id5.
```

Literal multiplication gives

```text
R0 = H A0 H E1,
R2 = H^-1 C0 H A1,
R4 = H^-1 C1 H^-1 E2,
K  = H^-1 B0 H^-1 B1 H E3 H^-1 E4 H^-1 E5 H E6 H^-1 E7.
```

The compiler prints every syllable and every copy retraction.  The four
retractions of `R2` first give

```text
g0=1,  g5=g3^-1,  g6=g4^-1 g2^-1.
```

The remaining retractions are equivalent to

```text
(g9 g11)^2=(g10 g12)^2=(g13 g1 g7)^2=g8^2=1,
g3=g8 (g13 g1 g7)^-1 g13 g8,
g4=(g9 g11) g1^-1 g13^-1 (g9 g11).
```

Thus one may retain the free slots `g9,g10,g13,g1,g2` and the four
involutions `g9g11,g10g12,g13g1g7,g8`.  This is only the projection
compression: the three full free-product carrier words must still be imposed
by the all-maximal forest/state-semiring calculation before classifying the
boundary.
