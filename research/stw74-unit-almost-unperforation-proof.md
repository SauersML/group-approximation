---
rg: 2
id: stw74-unit-almost-unperforation-proof
kind: route
title: Apply unit comparison to each finite root of the properly infinite unit
target: stw74-unit-almost-unperforation-closes-hinge
requires:
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
  - stw74-property-sp-is-the-exact-missing-condition
---

The unit `u` is properly infinite, so `(n+1)u=u` for every `n>=1`.  Let
`0!=x` in `Cu(A)`.  The finite-unit-root theorem gives an `n` with `n x=u`.
Consequently

```text
(n+1)u = u = n x.
```

Condition (UAU) gives `u<=x`.  The properly infinite unit is the largest
element of `Cu(A)`, as shown in `stw74-finite-unit-root-proof`, so `x<=u` and
hence `x=u`.

Thus every nonzero positive element has the same Cuntz class as the unit.  In
particular every nonzero hereditary subalgebra contains a projection
equivalent to the unit, by the standard fact that a projection Cuntz below a
positive element is equivalent to a projection in its hereditary subalgebra.
This is property (SP), and
`stw74-property-sp-is-the-exact-missing-condition` makes `A` purely infinite.

Finally, ordinary almost unperforation says

```text
(n+1)a <= n b  implies  a<=b
```

for all `a,b`.  Taking `a=u` and `b=x` gives (UAU), proving the stated
special case.
