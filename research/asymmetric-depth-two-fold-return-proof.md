---
rg: 2
id: asymmetric-depth-two-fold-return-proof
kind: route
title: Fold the private prefix leaves and retain the total occurrence gauge
target: asymmetric-depth-two-fold-return-retains-external-gauge
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - one-singer-square-does-not-identify-external-return-gauge
---

For each prefix leaf `w`, the Steinberg relation gives

```text
[x_(a,k_w)(s_w),x_(k_w,b)(t_w)]=x_ab(s_wt_w)=x_ab(e_w).
                                                               (DTRP1)
```

All outputs lie in the same additive root subgroup, so their product is the
root whose coefficient is the sum of the `e_w`.  The binary completeness
relation iterated along a finite complete prefix code says that this sum is
one.  This proves `(DTR3)` and `(DTR7)` as literal elementary-group word
identities.

Restriction of equal group elements to any representation and any reducing
carrier is equal.  Hence the normal form `(ERN4)` of `x_78(1)` is also the
normal form of `R`, proving `(DTR4)`.  Conjugating `(DTR3)` by `J` proves
that `(DTR5)` is exactly the old external-return naturality square.  Its
source and target chart normal forms are

```text
R=N tensor E,       J=M tensor D,
R'=N' tensor E',                                      (DTRP2)
```

and the fixed label equality `MN=N'M` cancels from `(DTR5)`, leaving
`DE=E'D`, equivalently `(DTR6)`.

The three private commutators do not define endomorphisms of `QH`; only
their complete product does.  Introducing intermediate charts can assign
gauges to the private arrows, but those are groupoid coboundaries and their
ordered product is forced to be the single `E` in `(DTR4)`.  Thus counting
the three written commutators as three same-carrier gauge occurrences would
be an occurrence-typing error.
