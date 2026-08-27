---
rg: 2
id: partial-whitehead-finite-model-proof
kind: route
title: Collapse the prefix partial equivalence to one finite-field corner and separate the local amalgam
target: partial-whitehead-cell-has-marked-finite-model
requires: []
---

Substituting `e=f=x=y=1` makes the two inverse relations in `(PWM1)` equal
to `1=1`, every support relation equal to `1=1`, and every complementary
support relation equal to `0=0`.  This proves that `(PWM2)` is well defined.
Functoriality of elementary matrices sends every authenticated coefficient
root `x_ij(r)` to `x_ij(epsilon(r))`; hence every Steinberg relation and every
coefficient equality used in the finite fragment remains exact.

The active unit maps to `1`, so elementary-root injectivity proves `(PWM3)`.
Direct multiplication gives

```text
[[1,1],[0,1]][[1,0],[-1,1]][[1,1],[0,1]]
 =[[0,1],[-1,0]],                                      (PWP1)
```

which proves `(PWM5)` in odd characteristic.  The finite image is a subgroup
of the finite group `EL_n(k)`.  A nonidentity element has trace zero in its
left regular representation, giving marked distance `sqrt(2)`.

For `(PWM6)`, a finite graph of finite groups has virtually free fundamental
group and is residually finite.  For every nonidentity element of the finite
union `D union EL_n(k)`, choose a finite quotient separating it.  The product
of these finitely many quotients is injective on both vertex groups.  Left
translation by either embedded vertex group on the finite quotient is a
disjoint union of free orbits, so restriction of the quotient's regular
representation is a multiple of that vertex group's regular representation.
This proves all claimed marked and canonical-trace properties.
