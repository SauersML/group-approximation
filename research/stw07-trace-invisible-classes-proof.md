---
rg: 2
id: stw07-trace-invisible-classes-proof
kind: route
title: Unitize the stabilization, restrict models to a corner, and extend corner models through compact compressions
target: stw07-trace-invisible-classes-carry-hahn-banach
requires: []
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

1. Nuclearity, separability and quasidiagonality pass to `A tensor K` and its
   unitization.  A stable algebra has no nonzero bounded trace
   (orthogonal-copy argument), so every tracial state factors through `chi`.
   `chi` is a character, hence a quasidiagonal trace.
2. `K_0(A) -> K_0(E)` is split injective.  If `n x = [p]` in `K_0(E)` with `p`
   over `E`, the scalar image of `p` has rank `0`, so `p` is over `A tensor K`
   and `n x in K_0^+(A tensor K) = K_0^+(A)`.  The converse is immediate.
3. A faithful model `psi_n` of `E` restricts to the corner `A tensor e_11`
   as a faithful model of `A` with the same value on `x`.  Conversely, given a
   faithful model `phi_n` of `A` killing `x`, define on `A tensor K` the maps
   `a tensor T -> (phi_n tensor id)(a tensor P_(j_n) T P_(j_n))`, with `j_n`
   growing slowly enough to be asymptotically multiplicative on finite sets,
   and extend them unitally to `E`.  Adding the character `chi` as a
   one-dimensional direct summand keeps the norm on the scalars, and the
   value on `x` is unchanged.
