---
rg: 2
id: f-infinity-finite-cd-groups-type-f-via-hsiang
kind: route
title: "Hsiang's conjecture makes every F_infinity group of finite cd of type F"
target: f-infinity-groups-of-finite-cd-are-of-type-f
requires: [hsiang-reduced-k0-of-torsion-free-group-rings-vanishes, f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]
---

Let `G` be of type `F_∞` with `cd G < ∞`.

`G` is torsion-free. A nontrivial finite cyclic subgroup `C` has
`H^{2k}(C; Z) ≠ 0` for every `k ≥ 1`, so `cd C = ∞`. Cohomological dimension
does not increase on passing to subgroups (K. S. Brown, *Cohomology of
Groups*, VIII.2).

By [[hsiang-reduced-k0-of-torsion-free-group-rings-vanishes]],
`K̃_0(Z[G]) = 0`. So [[f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f]]
shows that `G` is of type F. QED

The implication is one-way. Problem 1.21 needs only the one class `σ(G)` to
vanish for each such `G`, not the whole group `K̃_0(Z[G])`.
