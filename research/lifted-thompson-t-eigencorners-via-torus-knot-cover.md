---
rg: 2
id: lifted-thompson-t-eigencorners-via-torus-knot-cover
kind: route
title: Pull the corona representation of T-bar back to the torus knot group K(3,4) along a -> x, b -> y, where z = x^4, and use the knot-group eigencorner
target: lifted-thompson-t-centre-has-commutant-eigencorners
requires:
  - lifted-thompson-t-is-a-torus-knot-group-quotient
  - torus-knot-group-k34-has-central-eigencorners
---

Let `rho : T̄ -> U(Q)` with `rho(z) != 1`.  By item 1 of
`lifted-thompson-t-is-a-torus-knot-group-quotient`, there are `a, b in T̄`
with `a^4 = b^3 = z` that generate `T̄`.  Put `X = rho(a)` and `Y = rho(b)`.
Then `X^4 = Y^3 = rho(z) != 1`.

By `torus-knot-group-k34-has-central-eigencorners`, there are a nonzero
projection `P in {X, Y}' ∩ Q` and `lambda != 1` with `rho(z) P = lambda P`.
By item 2 of the quotient claim, `{X, Y}' ∩ Q = rho(T̄)' ∩ Q`.  That is (EC).

**The route is not circular, and nothing is lost.**  The required claim is
about all pairs `X^4 = Y^3`.  It is used only on pairs that also satisfy the
three Thompson relators.  Every Thompson-specific difficulty of (EC) has
therefore moved into one statement about a fixed one-relator group.  The
open leaf that remains is `torus-knot-group-k34-is-matricially-stable`, or
directly `torus-knot-group-k34-has-central-eigencorners`.

**Full chain to the flagship.**  The chain is:

```text
thompson-t-has-full-mf-radical
  + torus-knot-group-k34-is-matricially-stable
  => (matricially-stable-groups-have-central-eigencorners)  torus-knot-group-k34-has-central-eigencorners
  => (this route)  lifted-thompson-t-centre-has-commutant-eigencorners
  => (lifted-thompson-t-not-mf-via-central-eigencorners)  lifted-thompson-t-is-not-mf.
```

The last step also uses
`central-eigencorners-die-over-full-radical-quotients` and
`lifted-thompson-t-perfect-centre-cubically-elliptic`.
