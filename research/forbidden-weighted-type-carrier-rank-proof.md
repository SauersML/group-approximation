---
rg: 2
id: forbidden-weighted-type-carrier-rank-proof
kind: route
title: Trim fewer than four dimensions in every forbidden isotypic piece
target: forbidden-weighted-type-carrier-coverage-is-rank-rounding
requires: []
---

Commutation `(FWC2)` makes every product in `(FWC3)` a projection.  For a
projection `R` of rank `r`, set

```text
r'=4 floor(r/4).
```

Choose any `r'`-dimensional subspace of `RH` and let `P` be its orthogonal
projection.  Then `P<=R` and

```text
0<=tr_d(R)-tr_d(P)=(r-r')/d<=3/d.                      (FWR1)
```

Sum `(FWR1)` over `Omega` and use `(FWC4)` to obtain `(FWC5)`.  Decompose
`PH` into four equal-dimensional summands.  The four block matrix units give
the `M_4` system; grouping the first two and last two summands gives an `M_2`
system, with first atoms of ranks `rank(P)/4` and `rank(P)/2`.  This proves
`(FWC6)`.

Under `(FWC7)`, Schur's lemma gives
`R=I_(V_lambda) tensor R_lambda`.  Apply the same construction to the
multiplicity projection `R_lambda`; discarding at most three multiplicity
dimensions discards at most `3 dim(V_lambda)` Hilbert dimensions, which is
bounded by `(FWC8)`.

For the final countermodel, irreducibility implies that the reducing
projections in the isotypic block are exactly
`I_(V_lambda) tensor P_0`.  If its range lies in the range of `(FWC9)`, then
for every nonzero `w in range(P_0)` the whole subspace
`V_lambda tensor Cw` would lie in `Cv tensor Cw`, impossible when
`dim(V_lambda)>1`.  Hence `P_0=0`.
