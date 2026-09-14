---
rg: 2
id: countable-ec-overgroup-union-of-chains-proof
kind: route
title: Adjoin solutions along a dovetailed enumeration of finite systems and take the union of the chain
target: countable-groups-embed-in-countable-existentially-closed-groups
requires: []
---

Fix `X` (all groups, or torsion-free groups).  Both classes are closed under
subgroups and under unions of chains.

Fix a bijection `pi: N x N -> N` with `pi(i, j) >= i` (Cantor pairing).

Build countable groups `G = G_0 <= G_1 <= ...` in `X`.  When `G_i` is
defined, list the finite systems of equations and inequations with constants
from `G_i` as `S_(i,0), S_(i,1), ...`.  There are countably many because
`G_i` is countable.  Stage `n` treats the pair `(i, j) = pi^(-1)(n)`, and
`i <= n` guarantees `G_i` already exists.

- If `S_(i,j)` has a solution in some group `K` in `X` with `K >= G_n`, choose
  one.  Put `G_(n+1) = <G_n, solution>` inside `K`.  It is countable, and it
  lies in `X` as a subgroup of `K`.
- Otherwise put `G_(n+1) = G_n`.

Let `H = union_n G_n`.  It is countable, and it is in `X`: any element of
finite order lies in some `G_n`.

Let `S` be a finite system with constants from `H` that has a solution in
some `K` in `X` with `K >= H`.
- Its constants lie in some `G_i`, so `S = S_(i,j)` for some `j`.
- At stage `n = pi(i, j)` we have `K >= H >= G_n`, so a solution was
  adjoined, and it lies in `G_(n+1) <= H`.

So `H` is `X`-e.c., and it contains `G = G_0`.
