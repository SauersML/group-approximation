---
rg: 2
id: torus-knot-group-k34-central-eigencorners-via-stability
kind: route
title: Lift the corona pair to exact pairs with A'^4 = B'^3, where the fourth power is exactly central, and take its spectral corner
target: torus-knot-group-k34-has-central-eigencorners
requires:
  - torus-knot-group-k34-is-matricially-stable
  - matricially-stable-groups-have-central-eigencorners
  - lifted-thompson-t-is-a-torus-knot-group-quotient
---

Let `X, Y in U(Q)` with `X^4 = Y^3 = u != 1`.  By item 3 of
`lifted-thompson-t-is-a-torus-knot-group-quotient`, this is a homomorphism
`Theta : K(3,4) -> U(Q)` with `Theta(x) = X`, `Theta(y) = Y` and
`Theta(c) = u`, where `c = x^4` is central.  Also
`Theta(K)' ∩ Q = {X, Y}' ∩ Q`.

Assume `torus-knot-group-k34-is-matricially-stable`.  Apply
`matricially-stable-groups-have-central-eigencorners` with `H = K(3,4)` and
the central element `c`.  It gives, for any `lambda in sp(u)` with
`lambda != 1`, a nonzero projection `P in {X, Y}' ∩ Q` with `u P = lambda P`.
Such a `lambda` exists because `u != 1`.
