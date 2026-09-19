---
rg: 2
id: native-weyl-return-gauges-have-s3-model
kind: claim
title: The expanded native Weyl square leaves an exact S3 return-gauge model
invalidates:
  - native-weyl-square-identifies-return-gauge
artifacts:
  - research/native-weyl-return-s3-proof.md
distinct_from:
  one-singer-square-does-not-identify-external-return-gauge: that leaves two commuting independent involutions after one covariance square; this expands the conjugator into its actual two root directions and obtains a noncommuting S3 gauge packet.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that closes the whole depth-one role menu abstractly in a Clifford group; this computes the smallest literal native Weyl word on the external-return coordinate pair and its exact gauge equations.
---

**ESTABLISHED ODD-PARITY FIREWALL.**  On the actual EL20 coordinate pair
`(7,8)`, put

```text
n=x_78(1),                 m=x_87(1),
w_78(1)=x_78(1)x_87(1)x_78(1)=nmn.                    (NWR1)
```

Over characteristic two these are involutions, `w_78(1)` is the permutation
of coordinates `7,8`, and direct `2 by 2` multiplication gives

```text
w_78(1)n w_78(1)^(-1)=m.                              (NWR2)
```

Thus `(NWR1)--(NWR2)` are not abstract covariance: they are the literal
root-position word and its full native mixed square.  Any other required
root-position transport is a product of the same fixed words

```text
w_ab(1)=x_ab(1)x_ba(1)x_ab(1),                        (NWR3)
```

and its mixed squares are obtained by conjugating root indices.

Let `D,E,F` be the reservoir factors of `w_78(1),n,m`, respectively.  On a
common source chart, the literal factorization and conjugacy impose

```text
D=EFE,                    F=DED^(-1).                  (NWR4)
```

All three factors are involutions.  Modulo two, `(NWR4)` has the desired
odd-parity effect: its first row equates the parity classes of `D,F`, and
its second equates those of `F,E`.  Hence the external-return and Weyl
gauges occur with unequal odd parity in the closed two-cell.

But operator cancellation does not follow from parity.  In the finite group
`S_3`, take

```text
D=(1 2),                 E=(2 3),          F=(1 3).    (NWR5)
```

Then

```text
EFE=D,                   DED=F,             D!=E,      (NWR6)
```

and `DE` is a nontrivial element of order three.  This is an exact model of
the expanded native Weyl word and its mixed square in which the two gauges
do not cancel.

The model extends the partial-Whitehead fold-return packet rather than
living in a disjoint label quotient.  Relabel its six permutation
coordinates so that its authenticated transporter `W=(4 6)` becomes the
swap `(7 8)`.  Interpret that `W` on the reservoir by `D`, interpret the
external return `x_78(1)` by `E`, and the opposite root `x_87(1)` by `F`.
The old factorization `W=UVU` remains exact by assigning the middle factor
the reservoir `D`; every old fold/intermediate/final commutator contains
each transporter together with its inverse and therefore has trivial
reservoir factor.  Equations `(NWR4)--(NWR6)` make the new literal Weyl
factorization and all its conjugacy squares exact.  The old marked
permutation remains nonidentity.

Consequently the smallest unequal-odd-parity closed word promotes the
commuting two-qubit escape to a nonabelian `S_3` escape; it does not supply
the identity reservoir bridge `(ESB2)`.  A successful next row must rule out
the order-three product `DE`, for example by a second native loop imposing
commutation or a distinct braid length on the same two gauges.  Merely
expanding all fixed root-position Weyl conjugators and their naturality
squares cannot do so: they only reproduce conjugate copies of `(NWR4)`.
No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis,
literature result, or local compilation is used.

## Attempts

- **Use mod-two occurrence parity.**  It correctly sees `D,E,F` in one odd
  class, but the three distinct reflections `(NWR5)` have that same parity
  class in the abelianization of `S_3`.
- **Use the factorization and conjugacy simultaneously.**  These are exactly
  the two reflection-conjugacy equations `(NWR4)`; their universal finite
  quotient is already nonabelian and does not identify the reflections.
- **Add all fixed root-position mixed squares.**  Defining every transported
  occurrence by literal conjugation in the same `S_3` packet makes every
  such square a naturality identity and leaves `(NWR5)` untouched.
- **Add a commuting external return through an `L_0` triangle.**
  `two-external-return-cell-has-finite-s3-model` shows that the triangle
  only requires the new gauge to commute with `E`; taking it equal to `E`
  leaves the old reflection pair `D,E` and their order-three product intact.

DERIVATION
native-weyl-return-s3-proof
