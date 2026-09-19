---
rg: 2
id: same-center-quarter-label-difference-quadratic-phase-proof
kind: route
title: Classify native same-center label words and test the quarter-difference truth table
target: same-center-quarter-label-difference-has-quadratic-phase-fence
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - controlled-pauli-corner-has-clifford-groupification
  - packet-dressed-shared-implementer-requires-one-outer-class
---

In the basis `(QLD1)`, a Pauli word has the form

```text
P_(a,b,c)|x>=(-1)^(c+a dot x)|x+b>.                    (1)
```

An adjacent Whitehead permutes coordinates.  Conjugating `(1)` by a
coordinate permutation merely permutes `a` and `b`.  The set of maps `(1)`
together with coordinate permutations is closed under multiplication, so
induction on word length proves `(QLD3)` for every word in `(QLD2)`.

Suppose such a word had the action `(QLD5)`.  Comparing the basis vectors
on the two sides forces its affine permutation part to be exactly
`x |-> (x_2,x_1,x_3)`, so `b=0` and `pi=(1,2)`.  Its phase would then obey

```text
c+a_1x_1+a_2x_2+a_3x_3=x_1x_2                       (2)
```

for every `x`.  Set `x_3=0` and sum `(2)` over
`(x_1,x_2)=(0,0),(1,0),(0,1),(1,1)`.  Every affine term occurs an even
number of times, so the left side is zero in `F_2`; the right side is one.
This contradiction proves `(QLD6)`.

The controlled-Pauli groupification theorem gives the first formula in
`(QLD7)`, while the same-center Whitehead normal form gives the second.
Multiplication proves `(QLD8)`, and tensor-factor uniqueness proves that
its reservoir factor is the identity exactly when `(QLD9)` holds.
Finally `packet-dressed-shared-implementer-requires-one-outer-class` shows
that the CZ and adjacent-swap covariances cannot acquire this common gauge
merely by dressing one occurrence with packet words.  Thus `(QLD9)` is a
new cross-outer occurrence condition rather than an omitted simplification
of the established packet.
