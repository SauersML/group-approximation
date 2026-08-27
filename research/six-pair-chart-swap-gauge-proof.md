---
rg: 2
id: six-pair-chart-swap-gauge-proof
kind: route
title: Use two independent three-qubit blocks and a signed chart swap
target: six-pair-chart-swap-retains-external-gauge
requires:
  - external-weyl-dressed-native-pair-is-root-valued
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - root-valued-overlap-does-not-undress-external-selector
---

The root commutator formula and `a_mb_m=q` give `(SCG2)` when the two
middle indices agree; distinct middle indices give commuting root
rectangles.  Weyl conjugation gives `(SCG3)`.  Since `h` has indices
`{1,2,3,4}` and each `W_i` has indices in `{7,8,9}`, they commute.  Applying
this commutation to the original covariance table proves the same adjacent
scale action on the moved chart, hence `(SCG4)`.

For the finite model, let the first three binary coordinates label the
original chart and the last three label the moved chart.  Put `A_m=X_m`,
`B_m=Z_m`, `A'_m=X_(m+3)`, and `B'_m=Z_(m+3)`.  The two blocks cross-commute,
so their cross-center signs are `R=S=+1`, while every own-pair commutator is
`-1`, realizing `z=C=-1`.

Let `L_1` swap coordinates `1,2` in both blocks, let `L_2` swap coordinates
`2,3` in both blocks, and let `H` swap the two blocks.  Then

```text
L_1^2=L_2^2=H^2=1,
L_1L_2L_1=L_2L_1L_2,
[H,L_i]=1.
```

Take `W_i=L_i` and `h=-H`.  The scalar sign disappears from every
conjugation row and `(-H)^2=1`, so the whole displayed table is exact.  It
remains once in `g_2=hW_2`, giving `(SCG5)`.  Since a scalar lies in the
commutant of the full `M_64(C)` label algebra, every mixed-Pauli commutator
test is exactly zero.  The MSI-only artifact checks the six-coordinate
commutation matrix and all permutation relations.

