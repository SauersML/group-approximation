---
rg: 2
id: torsion-free-virtually-z-linear-groups-are-z-linear-proof
kind: route
title: Induce the integral representation from the finite-index subgroup
target: torsion-free-virtually-z-linear-groups-are-z-linear
requires: []
---

Let `M = Z^m` be the `Z[H]`-module given by `rho`, and let
`W = Z[G] ⊗_{Z[H]} M` be the induced module. Choose left coset
representatives `g_1 = 1, g_2, ..., g_d` of `H` in `G`. Since `Z[G]` is a free
right `Z[H]`-module on the `g_i`, `W` is free abelian on `g_i ⊗ e_j`
(`1 <= i <= d`, `1 <= j <= m`). `G` acts on `W` by left multiplication. This
gives a homomorphism `pi: G -> Aut_Z(W) = GL_(md)(Z)`.

Let `K = ker(pi)`, a normal subgroup of `G`.

1. `K ∩ H = 1`. The subgroup `1 ⊗ M = {1 ⊗ v}` is `H`-stable, because
   `h(1 ⊗ v) = h ⊗ v = 1 ⊗ rho(h)v` for `h in H`. The map `v -> 1 ⊗ v` is
   injective, since `W` is free on the `g_i ⊗ e_j` with `g_1 = 1`. So if
   `h in K ∩ H`, then `rho(h)v = v` for every `v`, hence `rho(h) = 1`, hence
   `h = 1`.
2. `K` is finite. If `k, k' in K` and `kH = k'H`, then `k'^{-1}k in K ∩ H = 1`.
   So `K` injects into the `d` cosets of `H`, and `|K| <= d`.
3. `G` is torsion-free, so the finite subgroup `K` is trivial.

So `pi` is injective. ∎

Torsion-freeness is used only in step 3; without it the proof still gives a
representation whose kernel is a finite normal subgroup meeting `H` trivially.

Model check: `G = Z`, `H = 2Z`, `rho(2k) = [[1, k], [0, 1]]`. Then `d = 2`,
`W = Z^4`, and the generator of `G` swaps the two copies of `Z^2` while its
square acts as `rho(2)` on each, so the induced map is injective, as the claim
predicts.
