---
rg: 2
id: leavitt-second-nielsen-direct-bridge-collision-no-go-proof
kind: route
title: Compare stable-letter normal forms and force both sign-change gates to be trivial
target: leavitt-second-nielsen-direct-bridge-collision-no-go
requires:
  - leavitt-nielsen-collision-has-a-hidden-first-side-relation
  - leavitt-nielsen-collision-no-four-cell-disk
---

For a `++++--` length-six paired presentation, write the two relators in the
abstract corner form

```text
x z h z y z^(-1)=1,
u z v z k z^(-1)=1.
```

Put `s=z^(-1)` and eliminate the bridge corners `h,k`.  In the free product
of the exact base-corner group with `<s>`, their images are

```text
psi(h)=s x^(-1)s^(-1)y^(-1)s,
psi(k)=s v^(-1)s u^(-1)s^(-1).                       (SN1)
```

Assume first that `x,y,u,v` are nonidentity.  The reduced stable-letter sign
sequences in `(SN1)` are respectively

```text
(+,-,+),       (+,+,-).
```

Free-product normal-form uniqueness makes equality impossible, regardless of
relations internal to the base-corner group.

The identity cases are also rigid.  Reducing `(SN1)` shows that equality can
occur only when

```text
y=1,  u=1,  v=x^(-1),                                (SN2)
```

or when all four fixed corners are trivial.  In the Leavitt slot rewrite,
`y` and `u` are precisely the two cyclic sign-change gates `E_0` and `A_1`.
Thus `(SN2)` makes both sign-change coefficients identities.  The adjacent
`t t^(-1)` pairs then freely cancel, so the purported word is not a reduced
length-six candidate at all.

Consequently no reduced `++++--` length-six word can create an actual
second-side kernel merely by making the two eliminated bridge images equal.
The earlier packet move collided the **first** edge map because it did not
respect this stable-letter obstruction.

There is a further direction constraint.  Even a second-side word whose
coefficient image is a nontrivial mixed normal form in `G_0*G_1` need not
kill either copy.  The synthesis target must map to a nonidentity word in one
`G_i` (or come with a separate simplicity argument forcing such a word).
The most economical remaining architecture is therefore relation transport:
identify two generators of a copy carrying an exact relation with a distorted
pair in another copy on which that relation is nontrivial.  The normal-form
calculation above proves that this requires either a different sign type or
more than the two affine bridge identifications available in `(SN1)`.
