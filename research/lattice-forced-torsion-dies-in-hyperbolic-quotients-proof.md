---
rg: 2
id: lattice-forced-torsion-dies-in-hyperbolic-quotients-proof
kind: route
title: A homomorphism kills the normal closure of whatever it kills, and hyperbolic groups contain no Z^2
target: lattice-forced-torsion-dies-in-hyperbolic-quotients
requires: [kapovich-wise-rf-iff-finite-quotients]
---

**Setup.** `N` has no nontrivial finite quotient, so every homomorphism from `G` to a
finite group kills `N`, hence `<<N>>`, hence `s`. So `s in R_f(G)`.

**Item 1.** If `π(N) = 1` then `π(<<N>>) = <<π(N)>> = 1`, so `π(s) = 1`. Hence
`π(s) != 1` forces `π(N) != 1`. `π(N)` is a quotient of `N`, so it has no nontrivial
finite quotient. If `Q` were residually finite, its subgroup `π(N)` would be too, and
being nontrivial it would have a nontrivial finite quotient: a contradiction.

**Item 2.** Let `K = ker(π|_N)`.
- If `K = 1`, then `π(N) ≅ N` contains `Z^2`. A word-hyperbolic group contains no
  subgroup isomorphic to `Z^2`, so this is impossible.
- So `K != 1`, and since `N` is simple, `K = N`, `π(N) = 1`, and `π(s) = 1` by item 1.

Torsion-free simple lattices in products of two trees contain `Z^2`: a product of
hyperbolic elements of the two factors in the lattice spans a flat. This fact is used
only to place the named examples in the hypothesis, not in the argument.

**Item 3.**
- (=>) is item 1 applied with `G = Q`, `π = id` and `s` any nontrivial element of `N`.
- (<=) By `kapovich-wise-rf-iff-finite-quotients`, a non-residually-finite hyperbolic
  group yields an infinite hyperbolic group `Q` without nontrivial finite quotients;
  take `N = Q`.
