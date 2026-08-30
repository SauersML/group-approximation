---
rg: 2
id: stw74-weak-cancellation-finite-root-proof
kind: route
title: Cancel all but one copy from a compact finite-unit-root identity
target: stw74-weak-cancellation-closes-hinge
requires:
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
  - stw74-property-sp-is-the-exact-missing-condition
---

Put `u=[1_A]` and let `0!=x` in `Cu(A)`.  Choose `n>=1` with `n x=u`.
There is nothing to prove if `n=1`.  Otherwise set `c=(n-1)x`.  Since `u` is
the compact largest element and is properly infinite,

```text
u+c = u << u = x+c.
```

Weak cancellation gives `u<<x`, and in particular `u<=x`.  Since `x<=u`,
we get `x=u`.

Thus every nonzero Cuntz class is the unit class.  As in
`stw74-unit-almost-unperforation-proof`, a projection Cuntz below a positive
element is equivalent to a projection in its hereditary subalgebra.  Hence
every nonzero hereditary subalgebra contains a projection, and property (SP)
plus the LXXIV hypothesis makes `A` purely infinite.

For comparison, in the truncated-soft-interval semigroup take a soft `x` and
the same `c=(n-1)x`.  Then `u+c=u<<u=x+c`, while `u` is not below `x`; this
is an explicit failure of weak cancellation.
