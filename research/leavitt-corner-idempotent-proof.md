---
rg: 2
id: leavitt-corner-idempotent-proof
kind: route
title: Two involutions multiply to an order-three unit; its two nontrivial powers sum to the corner
target: leavitt-corner-idempotent-unital-surjection
requires: [leavitt-unit-group-algebra-surjects-onto-leavitt]
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Why sufficient

The prerequisite supplies surjectivity of `pi : F_2[U] -> R`; everything else
is computation in characteristic two.

**The unit has order three.**  `x = s_0t_1` and `y = s_1t_0` satisfy
`x^2 = s_0(t_1s_0)t_1 = 0` and likewise `y^2 = 0`, while
`xy = s_0(t_1s_1)t_0 = s_0t_0` and `yx = s_1(t_0s_0)t_1 = s_1t_1`, so
`xy + yx = 1` is the idempotent relation.  In characteristic two
`(1+x)(1-x) = 1 - x^2 = 1` reads `u = u^-1`, and likewise `v = v^-1`, so
`g = uv` has `g^-1 = vu` and

    g + g^-1 = (1 + x + y + xy) + (1 + y + x + yx) = xy + yx = 1.

Multiplying by `g` gives `g^2 + g + 1 = 0`, hence `g^3 = 1`; and `g != 1`
because `g = 1` would give `g + g^-1 = 0 != 1`.  So `g` has order exactly
three and `g^2 = g^-1 != g`.

**The idempotent.**  In `F_2[U]`,
`e^2 = [g^2] + [g^3] + [g^3] + [g^4] = [g^2] + [g] = e`, the two middle terms
cancelling in characteristic two.  It is nonzero since `g != g^2`.  Its image
is `pi(e) = g + g^2 = g + g^-1 = 1_R`.

**Unitality and surjectivity of the restriction.**  `e A e` is a ring with
identity `e`, and `pi_e = pi|_(eAe)` sends `e` to `1_R`.  Given `r` in `R`,
surjectivity of `pi` gives `a` with `pi(a) = r`, and then

    pi_e(e a e) = pi(e) pi(a) pi(e) = 1 . r . 1 = r.

So `pi_e` is onto.

**Augmentation.**  `eps(e) = eps([g]) + eps([g^2]) = 1 + 1 = 0`, so `eps`
restricted to `eAe` is identically zero and in particular is not a unital map
on the corner.  Conversely, for an idempotent `f` with `eps(f) = 1` the
restriction `eps|_(fAf)` *is* unital into the domain `F_2`, and
`augmentation-blocks-leavitt-family-proof` (scalar half, with `Z` replaced by
`F_2`) forbids a unital binary Leavitt family in `fAf`.  Taking `f = 1` gives
the same verdict for `F_2[G]` itself, for every group `G`.
