---
rg: 2
id: endpoint-external-order-four-s3-breaker-proof
kind: route
title: Multiply the endpoint partial swap with the two constant root transvections
target: endpoint-external-order-four-is-conditional-s3-breaker
requires:
  - native-weyl-return-gauges-have-s3-model
  - eight-external-returns-have-no-whitehead-gauge-lock
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
  - endpoint-order-five-actor-has-half-gram
---

Write

```text
e=s_00t_00,       f=s_000t_000,
c=s_000t_00,      d=s_00t_000.                       (1)
```

Then `dc=e`, `cd=f`, and the endpoint partial Whitehead `P=What_(8,2;2)`
is the characteristic-two swap between `eR` in coordinate `8` and `fR` in
coordinate `2`, acting identically on their complements.  Direct block
multiplication gives

```text
P n P = x_72(d)x_78(1-e),
P m P = x_27(c)x_87(1-e).                             (2)
```

The two factors on either right-hand side commute.  Root additivity and
`n^2=m^2=1` therefore give

```text
(Pn)^2=x_72(d)x_78(e),
(Pm)^2=x_27(c)x_87(e).                                (3)
```

Each right-hand side of `(3)` is a nonidentity involution: its two nonzero
coefficients occur in distinct root positions, and `c,d,e` are nonzero
Leavitt matrix units.  Hence `Pn` and `Pm` have exact order four.  A second
direct multiplication with `w=nmn` gives `(Pw)^6=1`, while its square and
cube are nonidentity, so `Pw` has exact order six.  The MSI-only artifact
replays `(2)--(3)` and all three exact orders using faithful sparse Leavitt
normal forms.

Now suppose the four occurrences are represented on one homogeneous carrier
as fixed label operators tensored with reservoir factors `H,D,E,F`, and that
the fixed label operators themselves inherit the literal word rows.  Peeling
off the label factor in `(Pn)^4=1` gives `(HE)^4=1`.  The native Weyl cell
already gives `(DE)^3=1`.  Under `H=D`, the same element `DE` has orders
dividing both three and four, hence equals one.  Substitution into the two
native reflection equations gives `D=E=F`.

For the scoped countermodel without `H=D`, put `H=1` and use the three
standard reflections `(EOF6)`.  The new cross rows reduce to fourth or sixth
powers of involutions and are exact.  All endpoint-only gauges may be taken
to be one, while the existing eight-return model supplies the remaining
transported occurrences.  This proves both the conditional breaker and the
precise scope fence.
