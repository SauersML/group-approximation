---
rg: 2
id: b7-conjugacy-clock-normal-form-proof
kind: route
title: Reduce every B7-normalizing clock to a finite-by-cyclic normal form
target: b7-normalizing-conjugacy-clocks-are-residually-finite
requires:
  - b7-faithful-two-cell-retains-or3-prefix-defect
  - exact-fd-wandering-reflection-promotion-can-remain-sofic
---

Move every occurrence of `t` to the right using
`tk=alpha(k)t`.  Without a power relator this gives the unique semidirect
product normal form `kt^j`, `j in Z`.  If `r` is the order of `alpha`, then
`t^r` centralizes `K`; the subgroup it generates has index `r|K|`.
Finite-by-cyclic groups are residually finite here directly: reduce the
central exponent modulo arbitrarily large multiples and retain the finite
quotient `K semidirect C_(rM)`.

With `t^N=z`, the same collection process restricts the exponent to
`0,...,N-1`.  Conjugating the relation by `t` and conjugating elements of
`K` by `t^N` give exactly the compatibility conditions `(BCC3)`.  When they
hold, the collected normal forms form a finite group; when they fail, the
relations identify two distinct elements of `K`, so the packet does not
embed.

For several monomial clock returns, subtract clock exponents by the Euclidean
algorithm.  Either every exponent is zero, leaving `(BCC1)`, or a least
positive exponent remains and every other return is a consequence of it
plus a relation in `K`.  The preceding dichotomy applies.

Finally the exact artifact checks `(BCC5)--(BCC7)` over rational matrices.
The general residual-finiteness firewall then supplies the canonical
finite-quotient countermodels and the fixed value `(BCC4)`.
