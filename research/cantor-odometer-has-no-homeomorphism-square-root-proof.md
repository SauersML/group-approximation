---
rg: 2
id: cantor-odometer-has-no-homeomorphism-square-root-proof
kind: route
title: Homeomorphisms commuting with the odometer are translations, and 1 is not even in Z_2
target: cantor-odometer-has-no-homeomorphism-square-root
requires: []
---

Elementary. The Cantor set is homeomorphic to `Z_2` (Brouwer's
characterization), and `Z` is dense in `Z_2`.

1. **A root commutes with `a`.** If `t^2 = a`, then `t a = t^3 = a t`.
2. **Commuting with `a` forces a translation.** Let `h` be a homeomorphism
   with `h a = a h`.
   - Then `h a^n = a^n h` for every `n in Z`, i.e. `h(y + n) = h(y) + n`.
   - Fix `x in Z_2`. The maps `y -> h(x + y)` and `y -> h(x) + y` are
     continuous on `Z_2` and agree on the dense subset `Z`, so they agree
     everywhere.
   - Taking `x = 0` gives `h(y) = h(0) + y` for all `y`.
3. **The contradiction.** By steps 1 and 2, `t(y) = z + y` with `z = t(0)`.
   So `t^2(y) = y + 2z`, and `t^2 = a` forces `2z = 1` in `Z_2`. But `2Z_2` is
   the maximal ideal of `Z_2`, while `1` is a unit. So no `z` exists.

The equation `x^2 a^(-1) = 1` has exponent sum `2`. Its coefficient group is
infinite cyclic, hence hyperlinear, and the explicit overgroup root is given on
the claim.
