---
rg: 2
id: source-hecke-data-leave-projective-square-free
kind: claim
title: Scalar source Hecke data leave the first projective trace-square coefficient completely free
distinct_from:
  projective-far-defect-formula: that identifies the far limit of a fixed projectively central witness; this constructs tracial extensions with identical source and relative-Haar marginal data realizing every value of the first coefficient.
  canonical-trace-square-is-blind-to-iwahori-overlap: that gives a finite block-flip calibration for one selected projection direction; this is the higher-rank arithmetic source-extension calibration for the subgroup-central Haar unitary itself.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterizes matrix embeddability of the HNN extension; this shows why data internal to the scalar Gao source model cannot decide the mixed moment required by that characterization.
---

Put

```text
B=L(C) subset M=L(A),
C=SL_3(Z),       A=SL_3(Z[1/2]),
h=diag(2,1,1/2).
```

For every `s in [0,1]` there is a finite tracial extension `M subset P_s`
and a unitary `T_s in B' cap P_s` such that

```text
E_M(T_s^k)=0                    (k!=0),                 (SHF1)
|tau(T_s^* u_h T_s u_h^*)|^2=s.                        (SHF2)
```

All these extensions have the same embedded source inclusion, source
canonical trace, conditional expectations of source Hecke words, and
bifinite arithmetic Hecke tower.  They also have the same `B`-central Haar
marginal for `T_s`.  Only the mixed distribution of `T_s` against
`M minus B` changes.

The scalar in `(SHF2)` is the smallest projective positive-definite datum:

```text
phi_T(g)=|tau(T^*u_gTu_g^*)|^2
```

is positive definite and `C`-bi-invariant, and `(SHF2)` is `phi_T(h)`.
Therefore neither scalar coefficient elimination nor the orthogonal source
Hecke tower forces `phi_T(h)` toward one, or bounds the left side of `(PTS1)`
away from its maximal value.
Any successful projective transfer proof must use finite-coordinate
embeddability of the JOINT extension `(M,T)`, not a trace or
correspondence invariant internal to the scalar Gao source model.
