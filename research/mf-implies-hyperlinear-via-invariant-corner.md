---
rg: 2
id: mf-implies-hyperlinear-via-invariant-corner
kind: route
title: Compress to an invariant corner and read its own trace
target: mf-implies-hyperlinear
requires: [hyperlinear-elementwise-visibility, mf-invariant-corner-visibility, corner-renormalization-cost, countable-group-mf-conventions]
---

## Why sufficient

Fix `g != 1` in the countable MF group `G` and take `u`, `P` as in
`mf-invariant-corner-visibility`.  By `(I1)` the map `a |-> P u(a)` is a
homomorphism `G -> U(PQP)`.  A self-adjoint lift of `P` is asymptotically
idempotent, so continuous functional calculus lifts `P` to projections
`p_n`, nonzero along an infinite set of indices, and

```text
PQP = prod_n M_(r_n) / directSum_n M_(r_n),   r_n = rank(p_n) >= 1.
```

By `countable-group-mf-conventions` this homomorphism is carried by
operator-norm local models `v_n : G -> U(r_n)` whose defect tends to `0` on
every finite set --- by `(C1)` of `corner-renormalization-cost` the
compression cost in operator norm is nil, which is the only reason the
corner is usable no matter how small `r_n/d_n` is.  Operator-norm defects
dominate normalized Hilbert--Schmidt defects, and `(I2)` bounds
`Re tr_(r_n)(v_n(g))` away from `1`, so `g` is tracially visible.  Applying
this to every `g != 1` and invoking `hyperlinear-elementwise-visibility`
makes `G` hyperlinear.

## Not a restatement of the target

The prerequisite is a formally stronger sufficient statement, so this route
reduces rather than renames the target.  `mf-invariant-corner-visibility`
demands trace visibility *inside an operator-norm model*, which is
elementwise trace-controlled MF, whereas the target asks only for
Hilbert--Schmidt models.  No converse implication or separating group is
known.  In particular the evident attempt to combine an operator-norm model
with a Hilbert--Schmidt one does not supply a converse: their tensor or direct
sum is only Hilbert--Schmidt asymptotically multiplicative, so hyperlinearity
does not return operator-norm data by that operation.  The genuine step
performed here is the domination `||.||_2 <= ||.||_op` together with
elementwise assembly.

## Relation to the other route

This route needs no rate: the corner supplies visibility structurally rather
than by amplification.  Conversely `mf-implies-hyperlinear-via-rank-profile`
needs no invariant projection.  The two are the only mechanisms known here
for converting operator-norm separation into trace separation, and
`corner-renormalization-cost` shows they are governed by the same constant
`sqrt(d/r)`: an invariant corner pays it once, structurally, while a
functor pays it in the defect.
