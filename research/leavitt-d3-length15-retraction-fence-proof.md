---
rg: 2
id: leavitt-d3-length15-retraction-fence-proof
kind: route
title: Express the residual copy flux as one prefix times one tail
target: leavitt-d3-length15-retraction-fence
requires:
  - leavitt-d3-length13-k1-retraction-obstruction
  - leavitt-d3-length13-central-holonomies-are-conjugate
---

The length-fifteen exponent-three sign profiles are

```text
(1,1,13):15, (1,3,11):180, (1,5,9):450, (1,7,7):300,
(3,3,9):600, (3,5,7):2700, (5,5,5):760.
```

Consider the three unary profiles with two nonunary residuals of valence at
least three.  Rotate so that the first corner of one residual is the long
alternating source corner and the last corner of the other residual has the
three-syllable target form.  Let `A` be the product of the copy-2 source units
strictly between its two endpoints.  Retraction of the identity source
holonomy onto copies 2 and 1 gives

```text
g1 A=g2,                    g2 T=1,                     (1)
```

where `T` is the corresponding product of the intervening copy-1 units.
Thus `T=A^-1 g1^-1`.

For `(1,5,9)` and `(1,7,7)`, let `M` be respectively the remaining one-unit
or two-unit copy-2 tail in the common carrier.  Retraction of the common
carrier equality onto copies 0 and 1 gives a shared endpoint

```text
d=A M,                      Z=g0 d.                     (2)
```

Its copy-2 retraction is

```text
Z M Z^-1 g14 = Z T Z^-1 d.                              (3)
```

The target holonomy is `h` exactly when
`g0=h`, `g14=h g1^-1`.  Substitute this and `(1)`--`(2)` into `(3)`.  The two
sides share the prefix `h A M A^-1 g1^-1`; cancellation leaves

```text
1=M^-1 A^-1 h A M,
```

so `h=1`.

For `(1,3,11)` the tail `M` is empty.  In the representative
`--+-+-+-+-+++++`, the source identity retractions are explicitly

```text
g1 g3 g5 g7 g9 g11=g2,
g2 g4 g6 g8 g10=1.
```

The carrier retractions give

```text
d:=g12=g13=g3 g5 g7 g9 g11,
g14=Z(g4 g6 g8 g10)Z^-1d,       Z=g0d.
```

Putting `g0=h`, `g14=h g1^-1` again reduces the last equation to

`h g1^-1=h g1^-1d^-1hd`, hence `h=1`.

No normal-form branch was selected: equations `(1)` are consequences of the
source identity itself.  They therefore cover all Catalan cancellation
patterns.  If the source is instead the standard nonidentity central
palindrome, the same calculation leaves a conjugate of its central unit on
the left and a conjugate of the target central unit on the right.  The two
holonomies are conjugate, so in particular have equal order.
