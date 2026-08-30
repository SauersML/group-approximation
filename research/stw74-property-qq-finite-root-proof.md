---
rg: 2
id: stw74-property-qq-finite-root-proof
kind: route
title: Descend proper infiniteness through every finite unit root
target: stw74-property-qq-characterizes-pure-infiniteness
requires:
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
  - stw74-counterexample-has-uniform-root-towers
---

Put `u=[1_A]`.  The LXXIV hypothesis makes `u` properly infinite.  Let
`0!=x in Cu(A)`.  The finite-unit-root theorem supplies an integer `m>=1`
such that

```text
m x=u.                                                     (1)
```

If `Cu(A)` has property (QQ), then (1) makes `x` properly infinite.  Since
`x` is full, compactness of `u` gives `u<=N x` for some finite `N`.  Proper
infiniteness gives `N x=x`, and hence `u<=x`.  The properly infinite unit is
the largest element of `Cu(A)`, so `x<=u` and therefore `x=u`.

Thus `Cu(A)={0,u}`.  Equivalently, every nonzero positive element Cuntz
dominates the unit projection, which is Murray--von Neumann equivalent to a
projection in its hereditary subalgebra.  Hence `A` is purely infinite.

Conversely, if `A` is simple and purely infinite, then
`Cu(A)={0,u}`.  Its only nonzero element `u` is properly infinite, so
property (QQ) holds.

For the obstruction statement, let `A` be a counterexample and let `D` be
its full projectionless hereditary corner.  If `0!=a in D_+` and
`x=[a]`, then (1) holds for some `m`.  Were `x` properly infinite, the same
fullness argument would give `x=u`.  The unit projection would then be
Cuntz below `a` and hence equivalent to a nonzero projection in `Her_A(a)`,
contradicting `Her_A(a) subset D` and projectionlessness.  Therefore `x` is
not properly infinite while `m x=u` is.

Finally, `stw74-counterexample-has-uniform-root-towers` gives, for every
such `a`, classes `0!=x_1<<x_2<<...` and one integer `m` with `m x_k=u` for
all `k`, while no `x_k` dominates a nonzero projection class.  The preceding
argument shows that no `x_k` is properly infinite.  This is the asserted
uniform family of property-(QQ) failures.

Property (QQ) is used in the standard sense recorded by Joan Bosa,
*Stable Elements and Property (S)*, Definition 1.6.  The finite-root
collapse and the localized obstruction above are internal.
