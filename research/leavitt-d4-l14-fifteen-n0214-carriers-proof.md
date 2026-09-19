---
rg: 2
id: leavitt-d4-l14-fifteen-n0214-carriers-proof
kind: route
title: Compile and retract the normal fifteen-winner 0;214 system
target: leavitt-d4-l14-fifteen-n0214-carriers-are-explicit
requires:
  - leavitt-d4-l14-fifteen-winner-profile-has-five-classes
  - maximal-noncrossing-forest-criterion
---

For the ranker assignment

```text
T3 T4 T5 T6=id4^-1, T0 T1=id5, T2=id0^-1,
```

literal target matching gives

```text
R0=H A0 H E3,
R2=H^-1 C0 H A1,
R4=H^-1 C1 H^-1 E4 H^-1 E5 H E6 H^-1 E7,
K =H^-1 B0 H^-1 B1 H E1 H^-1 E2.
```

All copy retractions reduce to free coordinates `q,r,s,t,u` and one
involution `h`, with

```text
g0=1; g1=t; g2=u; g3=h s^-1; g4=h s t h;
g5=s h; g6=h t^-1 s^-1 h u^-1; g7=t^-1 s^-1 h;
g8=h; g9=q; g10=r; g11=q^-1h; g12=r^-1h; g13=s.
```

The compressed middle carrier has colors `3,2,3,2,3` and exactly two maximal
branches: `I: s=h` and `II: t=s^-1`.  In branch I the remaining carrier
lengths are `12,32`, the boundary length is `20`, and there are `70` combined
coordinate states.  In branch II the lengths are `12,30,32` and there are
`38` states.  MSI array `16682211` performs the exhaustive cyclic boundary
classification.
