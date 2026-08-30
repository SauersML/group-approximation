---
rg: 2
id: stw74-truncated-soft-interval-cu-proof
kind: route
title: Adjoin an isolated overflow point to a soft interval
target: stw74-cu-axioms-do-not-extract-projective-roots
requires: []
---

Define

```text
S = {0} union (0,1] union {u},
```

ordered as the displayed chain, with `u` strictly above the soft endpoint
`1`.  Addition has zero as identity and `u` as absorbing element, and for
soft `r,s` in `(0,1]` is defined by

```text
r+s = the soft real r+s,   if r+s<=1,
r+s = u,                   if r+s>1.
```

This addition is associative: a finite soft sum stays soft precisely when
its ordinary real sum is at most one, and otherwise it is `u`.  It is also
order preserving.

We verify the Cu axioms.  Increasing sequences entirely in the soft interval
have their ordinary supremum in `(0,1]`; a sequence has supremum `u` only if
one of its terms is already `u`.  Thus (O1) holds.  The way-below relation is

```text
0 << 0,
r << s  iff r<s                 for soft r,s,
r << u                           for every soft r,
u << u.
```

Every soft `s` is the supremum of a strictly increasing real sequence below
it, while `0` and `u` admit constant rapidly increasing approximations.  This
proves (O2).  The displayed description also proves (O3): below the overflow
threshold, strict inequalities add to a strict inequality; at or above an
overflow, every possible sum is way below `u`, including `u` itself.

For (O4), let `r_k` increase to a soft `r`.  If `r+s<=1`, ordinary addition
commutes with the supremum.  If `r+s>1`, then `r_k+s>1` eventually.  When
`r+s=1`, the soft sums increase to the soft endpoint `1`, rather than to
`u`.  Addition by `u` is immediate.  Hence addition preserves increasing
suprema.

For (O5), take `x'<<x<=y`.  The cases `x'=0` or `y=u` are settled by taking,
respectively, `z=y` or `z=0`.  In the remaining case all three elements are
soft and `x'<x<=y`; take the soft real `z=y-x'>0`.  Then

```text
x'+z=y<=x+z,
```

where the right-hand sum may overflow to `u`.  This is (O5).

For (O6), suppose `x'<<x<=y+z`.  There is nothing to prove when `x'=0`.
If either `y` or `z` is `u`, use `x` on that side and zero on the other.  If
`x=u`, then `y+z=u`; taking the two summands themselves works, including when
`x'=u`.  It remains that `x'` and `x` are soft and `y,z` are soft.  In ordinary
real arithmetic one has

```text
x' < x <= 1 < y+z       if y+z overflows,
x' < x <= y+z           otherwise.
```

Split the real number `x'` as `y'+z'` with
`0<=y'<=min(x,y)` and `0<=z'<=min(x,z)`; for example take
`y'=min(x',y)` and `z'=x'-y'`.  These inequalities give the required (O6)
decomposition.  (A zero summand is the zero of `S`.)

The rational soft points together with `0,u` form a countable basis.  Every
nonzero soft `r` has a finite multiple whose ordinary real value exceeds one,
so that multiple is `u`; hence every nonzero element generates all of `S` as
an ideal and `S` is simple.  Also `2u=u` and `u<<u`.  No soft `r` is compact,
because it is the supremum of a strictly increasing sequence below it.
Therefore the only compact elements are `0,u`, and a soft `r` dominates no
nonzero compact element.
