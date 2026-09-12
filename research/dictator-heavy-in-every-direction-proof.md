---
rg: 2
id: dictator-heavy-in-every-direction-proof
kind: route
title: Restrict a single coordinate to every affine-pair subcube at once
target: dictator-is-heavy-in-every-affine-direction
requires: []
---

Let `f = X_p` and `g = T_rho f = rho X_p`.  Fix `b != 0`.  On `D_b` the
coordinates are the cosets, and `X_p|_{D_b} = Y_{[p]_b}` where
`[p]_b = p + <b>` -- the character of the singleton `{[p]_b}`, since
`pi_b({p}) = {[p]_b}`.  Hence

```text
g|_{D_b} = rho * Y_{[p]_b},      Inf^{<=d}_{[p]_b}( g|_{D_b} ) = rho^2
```

for every `d >= 1` and every `b != 0`.  So all `N-1` directions carry a
heavy coset at the fixed level `delta = rho^2`, with `f` bounded by 1, of
degree 1, and with `T_rho` acting as multiplication by `rho`.

Two readings.

*No counting bound exists.*  Any argument concluding "at most `L(delta)`
directions can be heavy" is refuted by this one-line example.  In
particular the plan behind
`glue-lemma-via-parseval-budget-across-directions` -- spend the `L^2` budget
of `g` across the direction set -- cannot work: the budget here is
`||g||_2^2 = rho^2`, one unit, and it pays for all `N-1` directions at once
because the *same* Fourier coefficient serves every direction.  That is
exactly what a budget argument assumes cannot happen.

*What the lemma is really asking.*  Every heavy coset here contains `p`, so
`Q = {p}` gives `gamma = 1`.  The heavy directions are as numerous as
possible and their centres are as concentrated as possible, at the same
time.  `affine-orientation-glue-lemma` is the question of whether the second
is forced by the first.
