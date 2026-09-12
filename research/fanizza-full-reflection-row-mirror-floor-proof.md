---
rg: 2
id: fanizza-full-reflection-row-mirror-floor-proof
kind: route
title: Expand the two reflection blocks and isolate the mirror rank
target: fanizza-full-reflection-row-has-sharp-mirror-floor
requires:
  - fanizza-compressed-unitary-has-guarded-rank-floor
  - toeplitz-range-commutator-has-a-balanced-mirror-exit
---

Since `U R_E U^*=1-2Q` and both reflections are involutions,

```text
||R_F U R_E U^*-I||_2^2
 =||R_F-U R_E U^*||_2^2
 =4||Q-F||_2^2.                                          (FRP1)
```

Cyclicity gives

```text
ell=tr(E)-tr(EU^*FUE)=tr(E)-tr(FQ).
```

As `tr(Q)=tr(E)` and `tr(F)=tr(E)-h`, expanding `(FRP1)` yields

```text
||Q-F||_2^2
 =tr(Q)+tr(F)-2tr(FQ)
 =2ell-h,
```

which proves `(FRF1)`.  Also

```text
ell-h=tr(F)-tr(FQ)=||(1-Q)F||_2^2,
```

proving `(FRF2)--(FRF3)`.  Equality is equivalent to `(1-Q)F=0`, hence
`F<=Q`.  Then `C=Q-F` is a projection orthogonal to `F`, and its trace is
`tr(Q)-tr(F)=h`, proving `(FRF4)`.  Conversely every such `Q=F+C` attains
equality, including the balanced mirror construction in the required
Toeplitz claim.
