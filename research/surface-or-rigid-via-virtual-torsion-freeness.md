---
rg: 2
id: surface-or-rigid-via-virtual-torsion-freeness
kind: route
title: Pass to a torsion-free finite-index subgroup and apply Wilton's Corollary 6.4
target: one-ended-hyperbolic-groups-contain-surface-or-rigid
requires:
  - wilton-no-2-torsion-surface-or-rigid-subgroup
  - hyperbolic-finite-residual-is-torsion-free
  - finite-torsion-carrier-virtual-torsionfree-criterion
---

Let `Gamma` be a one-ended hyperbolic group.

1. **A torsion-free finite-index subgroup.**
   - A hyperbolic group has only finitely many conjugacy classes of finite subgroups. This is
     standard, and it is the same input as in `hyperbolic-virtual-torsionfree-via-finite-residual`.
   - Choose representatives `F_1, ..., F_r`. Then
     `finite-torsion-carrier-virtual-torsionfree-criterion` applies to `Gamma`.
   - By `hyperbolic-finite-residual-is-torsion-free`, `R_f(Gamma)` is torsion-free. That is
     condition (2) of the criterion.
   - Condition (5) then gives a torsion-free normal subgroup `Gamma'` of finite index.
2. **`Gamma'` satisfies Wilton's hypotheses.** It is quasi-isometric to `Gamma`, so it is
   hyperbolic and one-ended, and it has no 2-torsion.
3. **Apply Corollary 6.4.** By `wilton-no-2-torsion-surface-or-rigid-subgroup`, `Gamma'` contains
   a surface subgroup, or an infinite quasiconvex subgroup `R` of `Gamma'` admitting no splitting
   over a finite or virtually cyclic subgroup.
   - A surface subgroup of `Gamma'` is a surface subgroup of `Gamma`.
   - Otherwise, `R` is finitely generated and undistorted in `Gamma'`. `Gamma'` has finite index,
     so it is undistorted in `Gamma`, and the composite shows that `R` is undistorted, hence
     quasiconvex, in `Gamma`.
   - Being infinite and admitting no such splitting are properties of the abstract group `R`.
     So `R` is the required infinite quasiconvex rigid subgroup of `Gamma`.
