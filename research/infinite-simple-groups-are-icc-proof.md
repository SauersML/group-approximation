---
rg: 2
id: infinite-simple-groups-are-icc-proof
kind: route
title: Proof — a finite conjugacy class gives a proper finite-index normal subgroup
target: infinite-simple-groups-are-icc
requires: []
---
Let `G` be an infinite simple group. The center `Z(G)` is normal and proper (a
nontrivial simple group is not abelian unless it is cyclic of prime order, which is
finite), so `Z(G) = {e}`.

Take `g ≠ e` and suppose its conjugacy class is finite. Then the centralizer `C(g)`
has finite index. Its normal core `N = ⋂_{x ∈ G} x C(g) x⁻¹` is a normal subgroup of
finite index (an intersection of finitely many finite-index subgroups). Since `G` is
simple, `N = {e}` or `N = G`; `N = {e}` would make `G` finite, so `N = G`, i.e.
`C(g) = G` and `g ∈ Z(G) = {e}`, a contradiction. So every nontrivial conjugacy
class is infinite. So `G` is ICC and `L(G)` is a II_1 factor (Murray--von Neumann).
