---
rg: 2
id: modular-stratum-coordinates-via-spectral-alignment
kind: route
title: Align the central projections, complete finite-spectrum intertwiners, and truncate the resulting parameters
target: modular-strata-have-linear-coordinates-and-rank-splits
requires:
  - modular-vertex-charts-have-uniform-schatten-control
artifacts:
  - research/artifacts/modular-stratum-coordinate-coverage-2026-09-08.md
---

Equal generator multiplicities give equal ranks for the two central
involutions. Principal angles provide an off-diagonal logarithm `H_0`
with `exp(H_0) Z exp(-H_0)=Z'` and
`||H_0||_2<=pi||Z-Z'||_2/4<=pi delta/2`.

After aligning the center, the two corresponding generators differ
by at most `(1+pi)delta`. For equal-rank spectral projections `P_j,Q_j`,
the matrix `A=sum_j Q_j P_j` intertwines the finite-spectrum generators.
Its polar partial isometry completes within each matching spectral
label to a unitary intertwiner `W`. The artifact proves
`||W-I||_2<=2||U-U'||_2/gap`. A principal logarithm then gives
`||log W||_2<=pi||U-U'||_2/gap`. The within-center gaps are `2` for
the order-four generator and `sqrt(3)` for the order-six generator,
giving the stated common constant.

Even spectral truncation preserves the central commutation and
anticommutation conditions. Thus the truncated tuple still supplies
an exact representation under the prerequisite's parameterization.
Its operator movement is at most four times the cutoff. The endpoint
rank difference is at most the sum of the ranks of the four changed
exponential slots. Spectral counting bounds each rank by
`d||H_j||_2^2/theta^2`, yielding `(MSC2)`.
