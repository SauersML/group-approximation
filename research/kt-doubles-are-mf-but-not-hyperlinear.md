---
rg: 2
id: kt-doubles-are-mf-but-not-hyperlinear
kind: claim
title: The binary Kun-Thom doubles are MF but not hyperlinear
distinct_from:
  symmetric-double-weak-mf: That proves only operator-norm MF for arbitrary residually finite bases; this separates it from hyperlinearity for a specified family.
  kt-q2-double-is-not-hyperlinear: That supplies the negative half; this combines it with a faithful operator-norm model of the same double.
  mf-hyperlinear-radical-divergence: That witnesses an MF-invisible but hyperlinearly visible word; this gives the opposite direction of separation.
artifacts:
  - research/artifacts/mf-nonhyperlinear-double-separation-2026-09-20.md
---

For every r,d>=3, let

```
Gamma=EL_r(F_2[x_1,...,x_d]),
G=EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
D=G *_Gamma G.
```

With both polynomial inclusions as edge maps, D is an MF abstract group
in the operator-norm matrix-corona sense and is not hyperlinear.
Thus the class of MF groups is not contained in the hyperlinear groups.
No MF claim is made for either the full or reduced group C-star algebra.

The positive side uses Tatiana Shulman's symmetric-amalgamation theorem
and the repository's profinite-regular embedding argument. The negative
side uses Jihao Liu's internality theorem with Andreas Thom's conditional
normalization/double construction, on the pairs of Gabor Kun and Andreas
Thom. This is a downstream written-proof synthesis with those named
inputs, not an independent proof of Liu's analytic theorem or a Lean
certificate. No literature-priority claim is made.
