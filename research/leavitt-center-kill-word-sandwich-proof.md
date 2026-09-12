---
rg: 2
id: leavitt-center-kill-word-sandwich-proof
kind: route
title: Isolate the scalar part of a central Leavitt element with one kill-word sandwich
target: leavitt-center-is-coefficient-field
requires: []
artifacts:
  - GroupApproximation/Leavitt/BinaryLeavittSimple.lean
---

Write a central element `z` as a finite sum of monomials

```text
z=sum_i c_i s_(alpha_i)t_(beta_i)
```

and choose `r` bounding every word length.  Set `W=0^r1`.  Since
`t_Ws_W=1` and `z` is central,

```text
t_W z s_W=z.                                           (LCW1)
```

If `|alpha|,|beta|<=r`, prefix cancellation in a binary Leavitt family gives

```text
t_W(s_alpha t_beta)s_W in {0,1}.                       (LCW2)
```

A word of length at most `r` can be a prefix of `0^r1` only when it is a
string of zeroes.  After removing such a prefix, the remaining products
compare two words of the form `0^m1`; unequal such words are incomparable and
give zero, while equal words give one.  If the first prefix comparison fails,
the product is already zero.

Distributing `(LCW1)` over the finite monomial sum and applying `(LCW2)`
expresses `z` as a scalar multiple of one.  Conversely scalars are central,
so the center is exactly the base field.  Over `F_2`, every nonzero scalar is
one, hence every central unit is the identity.

This is formalized by `BinaryLeavitt.killWord_sandwich_monomial`,
`BinaryLeavitt.eq_smul_one_of_central`, `BinaryLeavitt.center_eq_bot`, and
`BinaryLeavitt.central_units_trivial`.  The proof uses no literature input.
