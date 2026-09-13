---
rg: 2
id: fp-simple-large-dehn-via-linear-quasi-retracts
kind: route
title: Put linear groups with large Dehn functions inside simple quasi-retract hosts
target: fp-simple-dehn-functions-realize-every-recursive-lower-bound
requires:
  - fp-linear-groups-realize-every-recursive-dehn-lower-bound
  - linear-groups-over-q-are-quasi-retracts-of-simple-groups
  - quasi-retracts-have-smaller-dehn-functions
---

Fix a recursive `f`.

1. **A linear input.** `fp-linear-groups-realize-every-recursive-dehn-lower-bound`
   gives a finitely presented `H <= GL_n(Q)` with `f(m) <= K delta_H(Km) + Km`.
2. **The host.** `linear-groups-over-q-are-quasi-retracts-of-simple-groups` gives
   a simple group `G` containing `H`, with the same finiteness properties and
   quasi-retracting onto `H`. Since `H` is of type `F_2`, so is `G`: `G` is a
   finitely presented simple group.
3. **Monotonicity.** `quasi-retracts-have-smaller-dehn-functions` gives
   `delta_H(m) <= K' delta_G(K'm) + K'm + K'`. Dehn functions vanish at `0`, so
   `delta_H(m) <= K' delta_G(K'm) + 2K'm` for all `m`.
4. **Compose.** With `K'' = 2K^2 K' + K` and `delta_G` non-decreasing,
   `f(m) <= K K' delta_G(K K' m) + (2K^2 K' + K) m <= K'' delta_G(K'' m) + K'' m`.

So `f ≼ delta_G`. `∎`

The premise in step 1 is open and conjectured false (Gersten–Riley). This route
records the exact coarse input the known technique needs; it does not make Problem
1.16 easier than that input.
