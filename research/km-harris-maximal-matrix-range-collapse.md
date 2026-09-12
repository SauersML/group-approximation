---
rg: 2
id: km-harris-maximal-matrix-range-collapse
kind: claim
title: Collapse the maximal matrix ranges of the explicit Kac-Moody Harris pair
distinct_from:
  compact-hyperbolic-km-regular-microstates-synchronize: that corrects canonical normalized-HS microstates using Curtis--Tits relations; this asks for uniform matrix-order approximation of all UCP images of one two-coordinate operator tuple.
  explicit-prs-harris-three-dimensional-system-has-lp: that permits any regular-dominating completion and states LP abstractly; this fixes the reduced completion of one explicit simple Kac--Moody group and replaces LP by a numerical matrix-range target.
---

**OPEN, CANDIDATE-SPECIFIC CLOSING CRITERION.**  Let `Gamma` be the explicit
rank-three `(2,4,6)` simple Kazhdan Kac--Moody lattice from
`simple-kazhdan-kac-moody-lattices-exist`, choose its finite root-subgroup
generating tuple, and put `A=C*_r(Gamma)`.  Form Harris's centered pair
`T_Gamma=(D-cI,G)` and its three-dimensional system `S_Gamma`.

Prove one, hence all, of

```text
gamma(T_Gamma)=1;
lim_k d_k(S_Gamma)=1;
W^(k-max)(W(T_Gamma)) -> W(T_Gamma)
  in Hausdorff distance uniformly over all matrix levels.       (KMH1)
```

By `harris-lp-is-maximal-matrix-range-collapse`, `(KMH1)` gives
`LP(S_Gamma)`.  The regular representation weakly contains itself and is
nonamenable because `Gamma` is infinite Kazhdan.  Therefore
`lp-of-harris-generator-system-forces-nonhyperlinear` makes this explicit
`Gamma` non-hyperlinear.

The `d_k` formulation is the most direct analytic target: prove a sequence
`epsilon_k->0` such that every unital `k`-positive map from the explicit
span `{I,D,G}` into an arbitrary operator system has cb norm at most
`1+epsilon_k`.  Equivalently, construct for every `epsilon>0` one finite
free spectrahedron `D_A` with

```text
(1-epsilon)D_A subset W(T_Gamma)
                     subset (1+epsilon)D_A.             (KMH2)
```

This is genuinely different from checking larger and larger finite output
levels separately: `(KMH1)` requires one estimate uniform in every output
matrix size.
