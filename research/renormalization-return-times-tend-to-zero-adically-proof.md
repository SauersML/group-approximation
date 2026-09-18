---
rg: 2
id: renormalization-return-times-tend-to-zero-adically-proof
kind: route
title: The odometer factor is continuous with brick-local digit maps, so it is local at linear depth and continuous along returns
target: renormalization-return-times-tend-to-zero-adically
requires:
  - renormalizable-thompson-elements-are-odometer-codes
---

**Item 1** is item 2 of `renormalizable-thompson-elements-are-odometer-codes`, with `e_i = T^i φ^{-1}`.
Then `e_i^{-1} = φ T^{-i}` on `T^i A`, which is the `S` above.

**Item 2**, by induction on `j`.
- `j = 1`: `π mod m` is `digit`, which is constant on the depth-`D` bricks making up the sets `T^i A`.
- Step: `π(x) mod m^{j+1}` is determined by `digit(x)` and `π(Sx) mod m^j`. By induction,
  `π(Sx) mod m^j` is constant on depth-`(D + (j-1)P)` bricks containing `Sx`.
- `x` lies in a depth-`D` brick of some `T^i A`, on which `S = φT^{-i}` is canonical. By the definition of
  `P`, the depth-`(D + (j-1)P)` brick of `Sx` is determined by the depth-`(D + jP)` brick of `x`.
- So `π mod m^{j+1}` is constant on depth-`(D + jP)` bricks.
- For the tape coding, the needed direction is "cells determine the brick". Every code word has length
  at least 1. So the state and the cells within radius `r(d) = d` of the head determine the depth-`d`
  brick in each coordinate: the first `d` bits of a coordinate come from at most `d` code words. Hence
  `π mod m^j` is a function of the state and the cells within radius `D + (j-1)P`. That is the radius
  form, with `a = D - P` and `b = P` (referee note N1).

**Item 3.** By continuity and item 1, `π(y) + n_i = π(T^{n_i} y) → π(y)` in `Z_m`, so `n_i → 0`. If
`m^j ∤ n_i` for all `i`, then `n_i` stays out of the neighbourhood `m^j Z_m` of 0, a contradiction. So no
height-`m` renormalization exists. ∎
