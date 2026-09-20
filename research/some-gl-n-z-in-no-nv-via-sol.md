---
rg: 2
id: some-gl-n-z-in-no-nv-via-sol
kind: route
title: If no hyperbolic Sol lattice embeds in any nV, then GL_3(Z) embeds in no nV
target: some-gl-n-z-embeds-in-no-brin-thompson-group
requires:
  - hyperbolic-sol-lattice-embeds-in-no-brin-thompson-group
---

Let `A = [[2,1],[1,1]] ∈ SL_2(Z)`, which is hyperbolic with eigenvalues `(3 ± √5)/2`. The integer
matrices `[[A^k, v], [0, 1]]`, with `k ∈ Z` and `v ∈ Z^2`, form a subgroup of `SL_3(Z) ≤ GL_3(Z)`.
It is isomorphic to `Z^2 ⋊_A Z`: the translations `v` form the normal `Z^2`, and conjugation by
the generator `[[A, 0], [0, 1]]` acts on it by `A`. A copy of `GL_3(Z)` in `nV` would contain this
Sol lattice. So `n = 3` witnesses the target.
