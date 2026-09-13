---
rg: 2
id: vtf-iff-chern-quillen-class-dies-on-finite-index-proof
kind: route
title: Torsion-free finite-index subgroups kill high degrees, and invisible torsion keeps the class alive
target: vtf-iff-chern-quillen-class-dies-on-finite-index
requires: [chern-quillen-class-detects-all-prime-order-torsion, finite-torsion-carrier-virtual-torsionfree-criterion]
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Full proof: artifact §3.

**(1 => 3).** Let `H` be a torsion-free subgroup of finite index. Stabilizers are
finite, so `H` acts freely on the contractible `d`-dimensional complex `X`, and `X/H`
is a `K(H,1)` of dimension `d`. Hence `H^q(H;F_p) = 0` for `q > d`. A Chern–Quillen
class has degree `N = 2(p-1)p^(a+e) >= 2p^(d-1) >= 2^d > d` when `d >= 1`. When
`d = 0`, `G` is finite and `H = 1`. So every such class dies on `H`.

**(3 => 2)** is trivial.

**(2 => 1) and persistence.** Every finite subgroup fixes a vertex, and there are
finitely many vertex orbits. So finitely many finite subgroups carry all torsion up to
conjugacy, and `finite-torsion-carrier-virtual-torsionfree-criterion` applies: if `G`
is not virtually torsion-free, `R_f(G)` contains some `x` of prime order `p`, and
`p | M`.

A finite-index `H` contains its normal core, which contains `R_f(G)`, so `P = <x>`
lies in `H`. For any Chern–Quillen class `c` at `p`,
`res^H_P(res^G_H c) = res^G_P c != 0` by
`chern-quillen-class-detects-all-prime-order-torsion`, and the same holds for
`c^(p^k)`. So no Chern–Quillen class at `p` dies on a finite-index subgroup, which
contradicts (2).
