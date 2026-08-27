---
rg: 2
id: exact-leak-refuted-by-projective-transfer
kind: route
title: The trace-square transfer inequality refutes the exact quasi-regular leak outright
target: no-exact-quasi-regular-leak
requires:
  - projective-commutant-transfer-for-arithmetic-pair
---

First the identity behind the route.  For `W in U(d)`, expanding in the
normalized Hilbert--Schmidt inner product on `M_(d^2)` with
`Ad(W) = W tensor conj(W)`:

```text
|| Ad(W) - I ||_2^2 = 2 - 2 Tr(Ad W)/d^2 = 2 - 2 |tr_d(W)|^2,
```

and `[Ad U, Ad V] = Ad([U,V])`, so

```text
|| [Ad U, Ad V] - I ||_2^2 = 2 - 2 |tr_d([U,V])|^2.
```

Now suppose an exact quasi-regular leak `(EQL1)` exists: microstates
`U_m` for `Gamma = SL_n(Z[1/p])` with regular restricted trace and a
unitary `K_m` exactly central for `pi(Lambda)` in the limit, with

```text
tau(K* pi(gamma) K pi(gamma)*) -> 0        (gamma notin Lambda).
```

Evaluate the two sides of `(PRT1)` at `U = K_m`:

- Right side: `e(K_m, U_m(c)) -> 0` for every `c in S`, because exact
  `Lambda`-centrality gives `[K_m, U_m(c)] -> I`, so
  `|tr([K_m, U_m(c)])| -> 1`.  The defect `delta_m -> 0`, so
  `eta(delta_m) -> 0`.
- Left side: the leak profile at `h notin Lambda` gives
  `tr([K_m, U_m(h)]) = tau(K* pi(h) K pi(h)*) -> 0` along the
  ultrafilter, so `e(K_m, U_m(h)) -> 1`.

Then `(PRT1)` reads `1 <= K * 0 + 0` in the limit — contradiction.  So
`projective-commutant-transfer-for-arithmetic-pair` implies
`no-exact-quasi-regular-leak`, and through
`non-hyperlinear-from-exact-quasi-regular-leak` it yields the explicit
non-hyperlinear group.

Note the margin: the leak needs `e(K, U(h))` to reach `1`, but any
uniform positive floor `e >= epsilon_0` bounded away from the inequality's
right side already kills it.  PRCC may therefore be proved in a much
weaker quantitative form than `(PRT1)` and still close this target: it
suffices that no `Lambda`-projectively-central unitary keeps
trace-square energy above a fixed threshold at `h`.  This is the
weakest inequality-shaped statement in the lane.
