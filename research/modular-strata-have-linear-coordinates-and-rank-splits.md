---
rg: 2
id: modular-strata-have-linear-coordinates-and-rank-splits
kind: claim
title: Each modular multiplicity stratum has linear-cost coordinates and exact operator/rank factorizations
distinct_from:
  modular-vertex-charts-have-uniform-schatten-control: that constructs an admissible forward map and a bounded lift of cocycles; this proves its full image is the generator-multiplicity stratum and bounds coordinates of every endpoint in that stratum.
  iwahori-torsion-multiplicity-stratum-reconciliation: that asks to reconcile different multiplicities while controlling compatibility defect; this assumes both endpoint representations are given and their generator multiplicities already agree.
  dilution-obstructs-flat-quadratic-iwahori-repair: that excludes universal flat parameter budgets on dilute errors; this permits concentrated parameters and separates a supplied change into an exact small-operator-norm leg and an exact small-rank leg.
artifacts:
  - research/artifacts/modular-stratum-coordinate-coverage-2026-09-08.md
---

Let `rho,rho':SL_2(Z)->U(d)` be exact representations with matrices
`S,B` and `S',B'` in the presentation `C_4 *_(C_2) C_6`.
Assume `S,S'` have the same eigenvalue multiplicities and likewise
`B,B'`. Put

```text
delta=max(||S-S'||_2,||B-B'||_2),
C=pi(1+pi)/sqrt(3).
```

There are anti-Hermitian parameters `H=(H_0,H_4,H_6)` in the natural
parameter space at `rho` such that

```text
Psi_rho(H)=rho',       ||H||_2<=C delta,       ||H||_op<=pi.       (MSC1)
```

Here `H_0` anticommutes with `Z=S^2=B^3`, while `H_4,H_6` commute
with it, and tuple norms are maxima. Conversely every endpoint of
`Psi_rho` has those same generator multiplicities. Thus this map
covers the whole multiplicity stratum. No continuity of the chosen
parameters, global inverse, or uniform inverse-chart radius is asserted.

For any `theta>0`, truncate each parameter spectrally to
`H_(j,lo)=H_j 1_(|H_j|<=theta)` and set `rho_lo=Psi_rho(H_lo)`.
Then `rho_lo` is an exact vertex representation and

```text
max_(g in {s,b}) ||rho_lo(g)-rho(g)||_op <= 4 theta,
max_(g in {s,b}) rank(rho'(g)-rho_lo(g))/d
    <= 4 ||H||_2^2/theta^2 <= 4 C^2 delta^2/theta^2.             (MSC2)
```

For example `theta=sqrt(delta)` gives an exact intermediate
representation with operator movement at most `4 sqrt(delta)` from
the first endpoint and normalized-rank movement at most `4C^2 delta`
from the second. The zero-distance case is immediate. The same
statements apply to pairs of vertices with maximum tuple norms.

Both endpoints are supplied. The theorem constructs no compatible
Iwahori endpoint, reconciles no unequal multiplicities, and asserts
no common reducing corner for all the rank differences. Applied to
two vertices, the intermediate pair remains exact on each vertex;
compatibility between the vertices need not be preserved.
