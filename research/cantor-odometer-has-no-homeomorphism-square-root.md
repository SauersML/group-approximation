---
rg: 2
id: cantor-odometer-has-no-homeomorphism-square-root
kind: claim
title: The dyadic odometer is not the square of any homeomorphism of the Cantor set
invalidates:
  - kl-via-internal-closure-of-a-universal-group
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asks for roots in overgroups; this exhibits a degree-two equation with coefficients in Homeo of the Cantor set that has no root inside that group, while its coefficient group Z solves it in an overgroup.
  infinite-symmetric-groups-miss-a-unimodular-root: that is the internal failure for Sym(Omega), already at degree one; this is the internal failure for Homeo of the Cantor set, at degree two.
---

Identify the Cantor set with the 2-adic integers `Z_2`, and let
`a(y) = y + 1` be the odometer. There is no homeomorphism `t` of `Z_2` with
`t^2 = a`. Equivalently, the nonsingular equation `x^2 a^(-1) = 1`, of
exponent sum `2`, has no solution in `Homeo(C)`.

The coefficient group `<a>` is infinite cyclic, so a root exists in an
overgroup. For example, on `Z_2 x {0, 1}` the map `(y, 0) -> (y, 1)`,
`(y, 1) -> (y + 1, 0)` squares to `a x id`, and `a -> a x id` is a faithful
copy of `<a>`.

## What it kills

Every countable group acts faithfully on a Cantor set: an infinite group by the
Bernoulli shift on `{0,1}^G`, a finite one on `{0,1}^(G x N)`. So internal
closure of `Homeo(C)` under nonsingular equations would prove
Kervaire--Laudenbach for all countable groups. This claim shows that internal
closure fails at degree two.

Together with `infinite-symmetric-groups-miss-a-unimodular-root` and
`cantor-homeomorphisms-miss-a-unimodular-root`, this invalidates
`kl-via-internal-closure-of-a-universal-group`. The unimodular case fails too,
by the second of those claims.
