---
rg: 2
id: iwahori-half-piece-and-independence-proof
kind: route
title: Freely reduce the two rows and evaluate two separating quotients
target: iwahori-torsion-frame-relators-have-a-half-piece
requires:
  - iwahori-two-triangle-torsion-normal-form
---

From `t=xa`, one has `t^(-1)=a^2x` and

```text
t^(-2)xb=(a^2x)^2xb=a^2xa^2b=r,
```

which proves `(THP1)`.  Substitution into `(xr)^2` is already reduced and
gives `(THP2)`.

For covariance, first expand

```text
rtr^(-1)t^(-4)
=a^2 x a^2 b x a b^2 a x a (a^2x)^4.
```

At the displayed junction, `a a^2` cancels, then `x x` cancels, and then
the newly adjacent `a a^2` cancels.  The remaining word is exactly `(THP3)`.
No adjacent syllables lie in the same free factor, so it is reduced.

Cyclically shifting `(THP2)` by its first `x` gives `u'`; direct comparison
with `(THP3)` gives the five-syllable common prefix `(THP4)`.  Since `u'`
and `v` are distinct elements of the symmetrized relator set, this is a
piece in the classical free-product sense and violates the strict
half-length bound for `u`.

Finally, under `a=b=1`, `(THP2)` is `1` and `(THP3)` reduces to `x`.  Under
`x=1,a=b=g` with `g^3=1`, exponent counting gives

```text
u |-> g,                    v |-> g^12=1.
```

These are the two claimed nonredundancy witnesses.

