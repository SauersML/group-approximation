---
rg: 2
id: thompson-t-quasi-retracts-onto-f-resolved
kind: claim
title: "Bridson's easier question resolved: decide whether Thompson's group F is a quasi-retract of Thompson's group T"
---

Part (f) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether there
are coarsely Lipschitz maps `i: F -> T` and `r: T -> F` with `r ∘ i` at bounded
distance from the identity.

This claim is the question. It is established only by a yes-route or a no-route
requiring the corresponding established answer claim; never by a
`requires: []` route. A yes-answer to part (c) gives a yes-answer here.

## Attempts

- **Cut the circle at the image of the base point.** With `i` the inclusion of
  `F = Stab_T(0)`, set `r(g) = R_{-g(0)} ∘ g`, where `R_θ` is the rotation by the
  dyadic angle `θ`. Then `r(g)` fixes `0`, so `r(g)` lies in F, and `r` is the
  identity on F. For a generator `s` of F, `r(gs) = r(g)s`. For the order-three
  generator `c`, `r(g)^{-1} r(gc) = g^{-1} R_δ g c` with `δ = g(0) - g(c(0))`, a
  conjugate of a rotation by `g`, whose length is not bounded. Dies: this `r` is
  not coarsely Lipschitz.
- **Obstructions inherited by quasi-retracts.** Type F_n and Dehn-function bounds
  pass to quasi-retracts (Alonso 1994). F is of type F_∞ with quadratic Dehn
  function (Guba), and T is of type F_∞ (Brown) with quadratic Dehn function
  (Migliorini, arXiv:2410.23088, as recorded in the list). Dies: no obstruction.
  Non-amenability of T does not pass to quasi-retracts (Z is a quasi-retract of a
  free group). Dies.
