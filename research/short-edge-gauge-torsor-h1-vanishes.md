---
rg: 2
id: short-edge-gauge-torsor-h1-vanishes
kind: claim
title: The finite source-table short-edge gauge torsor has quantitative first-cohomology vanishing
distinct_from:
  spherical-short-holonomies-admit-local-gauge: that is the geometric conclusion for shadow permutations on the spherical cloud; this claim isolates the abstract finite torsor/cohomology theorem needed after short relation holonomies are supplied.
  a3-cone-repairs-to-coboundaries-not-cocycles: that established firewall says the A_3 cone cannot preserve arbitrary global holonomy on a non-simply-connected target; this claim is only for the fixed finite source multiplication table and asks directly for vanishing of its relevant short-edge torsor class.
  relation-defects-obey-permutation-gauge-law: that gives the exact nonlinear change-of-gauge formula for one relation; this claim asks for simultaneous quantitative solvability of the whole finite system modulo its relations among relations.
artifacts:
  - research/artifacts/hyperlinear-cycle-synchronization-bypasses-2026-08-21.md
---

**OPEN.**  For every fixed finite regular-character multiplication table `T`
there is a finite relation-of-relations complex `K_T` and a constant `C_T`
with the following property.

Let `X={x_1,...,x_N}` be a spherical cloud and let `sigma_s in Sym(N)` be
shadow maps for the labels of `T`.  For every multiplication cell
`r=(g,h,k)` set

```text
delta_r=sigma_k^(-1) sigma_g sigma_h.                    (SGT1)
```

Give permutations the geometric displacement seminorm obtained from the
cloud after discarding an exceptional set of density `eta`; conjugation by a
shadow map transports this seminorm with only the already charged matching
error.  Regard `(SGT1)` with the gauge law

```text
c_k = delta_(g,h,k) (sigma_h^(-1)c_g sigma_h)c_h          (SGT2)
```

as an affine nonabelian torsor on `K_T`.

If all cell defects have displacement radius at most `rho` outside density
`eta`, and the exact syzygies among the multiplication cells give the trivial
class in the corresponding nonabelian `H^1` obstruction set, then there are
source gauges `c_s` solving `(SGT2)` outside density at most `C_T eta` and
moving every remaining source point by radius at most `C_T rho`.

Equivalently, after choosing a spanning tree in `K_T`, every fundamental-cycle
obstruction admits a bounded filling by the fixed multiplication 2-cells, and
the resulting products/conjugates of the `delta_r` have total geometric
length at most `C_T rho`.  The statement is quantitative because `T` is fixed:
all filling lengths and incidences are finite constants independent of the
cloud size and representation dimension.

The claim is intentionally **not** a general permutation-stability theorem.
It is a metric torsor-triviality statement for one fixed finite relation
complex and for the short-edge coefficient system forced by the spherical
matching construction.
