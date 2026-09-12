---
rg: 2
id: spectral-thresholds-and-polar-corners-repair-povm-cuts
kind: route
title: Sum spectral coarea before passing to direct-sum corners and polar-repaired source unitaries
target: low-energy-povms-yield-flexible-projection-cuts
requires: []
artifacts:
  - research/artifacts/low-energy-povm-flexible-cuts-2026-09-08.md
---

For a positive contraction `f`, the spectral weights
`tau(e_j K(e_k))` are nonnegative, symmetric, and have marginals
`tau(e_j)`. Weighted coarea over `(1/3,2/3)` therefore supplies
a threshold projection `r` with

```text
E_K(r)<=3sqrt(3 tau(f)E_K(f)).
```

Summing and using `sum_i tau(f_i)=1` gives total cut energy
at most `3sqrt(3eta)`. The scalar bounds

```text
1_(z>t)<=3z,
|1_(z>t)-z|<=3z(1-z),       1/3<t<2/3,
```

give `sum_i r_i<=3I` and
`||sum_i r_i-I||_1<=3gamma`. These control dimension and trace
without physically orthogonalizing the cuts.

For each corner inclusion `J_i:r_i C^d->C^d`, complete the
polar part of `r_i U_a r_i` to a unitary `V_(a,i)`. Its
column intertwining error has square at most
`||[U_a,r_i]||_2^2`. Assemble the inclusions into a row map
`J`, so that `JJ*=sum_i r_i`. A fixed-word telescoping bound
has error at most `L epsilon`. Although `J` need not be an
isometry, it preserves the Frobenius norm of a block-diagonal
operator when applied on the left. Together with
`JJ*<=3I`, this proves the relator estimate with the factor
`sqrt(3)` and the dimension normalization `sqrt(D/d)`.

Trace Cauchy--Schwarz controls the telescoping trace error by
`L epsilon/sqrt(D/d)`. The trace-norm estimate on `JJ*-I`
then contributes at most `6gamma/(D/d)`. This proves the
canonical trace estimate as well as the quantitative theorem.

The artifact proves all steps directly, including energy domination
for random-unitary averages, localization on a supplied seed corner,
and the precise limit on transferring a seed's minimum-rank property.
