---
rg: 2
id: modular-multiplicity-repair-by-common-central-surgery
kind: route
title: Change the common central sign on one small subspace before relabeling torsion spectra
target: modular-multiplicities-reconcile-at-quadratic-rank-cost
requires:
  - modular-strata-have-linear-coordinates-and-rank-splits
artifacts:
  - research/artifacts/modular-multiplicity-rank-reconciliation-2026-09-08.md
---

For finite-spectrum unitaries, the spectral-overlap identity bounds
half the L1 discrepancy of the eigenvalue multiplicities by the
squared unnormalized HS distance divided by the squared spectral
gap. Thus the generator discrepancies `t_S,t_B` satisfy
`t_S<=d delta^2/2`, `t_B<=d delta^2`. The discrepancy `k` of the
central positive multiplicities is at most either generator
discrepancy.

Choose a `k`-dimensional subspace `F` in the excess central-sign
space of the first representation. The cyclic spans of `F` under
`S` and `B` have dimensions at most `2k` and `3k`, since on that
central-sign space `S^2` and `B^3` are scalar. Within each span,
replace its generator so that `F` becomes reducing with the opposite
central sign. On the remaining part of that span preserve the old
central sign and all but `k` original eigenvalue labels. Outside the
span leave the generator unchanged. Both new generators therefore
have the same central involution, with the target central
multiplicities, while their own label multiplicities have moved by
at most `k`.

Relabel eigenvectors within each of these common central-sign
spaces to obtain the target generator multiplicities. This costs
rank at most `t_S+k` and `t_B+k`. The total ranks are consequently
at most `t_S+3k<=2d delta^2` and
`t_B+4k<=3d delta^2`. All vertex relations remain exact.
The inequality `||U-V||_2<=2sqrt(rank(U-V)/d)` gives `(MMR1)`.
The prerequisite supplies the chart coordinates to the second
endpoint once these multiplicities agree.

For `(MMR2)`, run the surgery in the opposite direction, obtaining
an exact `rho_hat` with the first endpoint's multiplicities,
rank distance at most `3d delta^2` from `rho'`, and HS distance at
most `K delta` from `rho`. Apply the prerequisite's exact
operator/rank factorization to `rho,rho_hat` and add the two rank
bounds. Fixed-word telescoping proves the claimed Iwahori residual
control. The artifact gives the full central-surgery construction,
the constants, and the endpoint and sharpness boundaries.
