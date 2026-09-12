---
rg: 2
id: four-cap-common-phase-mark-collapse-proof
kind: route
title: Compute the four cap Hecke coboundaries and globalize their parity equations
target: four-cap-common-phase-forces-trivial-mark
requires:
  - edgeful-or3-four-cap-walsh-packet
  - primitive-packet-corner-is-matrix-over-hecke-atom
  - central-hecke-controlled-multipaths-remain-sectorwise
---

In the matrix-over-Hecke identification, conjugating the translation
`T_phi` by `W_l=diag(h_(l,chi))` sends its `(chi+phi,chi)` coefficient to

```text
h_(l,chi+phi) h_(l,chi)^*.
```

This is `(FCP1)`--`(FCP2)`.  Replacing `chi` by `chi+phi` proves `(FCP3)`.
For two directions, both sides of `(FCP4)` telescope to

```text
h_(l,chi+phi_(l,j)+phi_(l,k)) h_(l,chi)^*.
```

This proves the asserted flatness without any commutativity assumption on
`H`.

Every point of `H_l` satisfies

```text
sum_(j:l_j=1) x_j=1 mod 2.
```

Hence the product of the corresponding diagonal coordinate signs is `-I`.
Common conjugation by `W_l` preserves the product identity, giving `(FCP5)`
with the selected central sign denoted by `J`.

Now assume the same three involutions `A,B,C` implement their named logical
variables independently of the cap.  From `AB=AC` multiply on the left by
`A` and use `A^2=1`, obtaining `B=C`.  The equation `BC=J` then gives
`J=B^2=1`.  If `ABC=J` also holds, the pair equations give `A=B=C`, and so
`A=ABC=J=1`.  This is an identity in the abstract presented algebra, so it
does not depend on a matrix evaluation or on a packet retraction.

Finally, if the equations are instead compressed by orthogonal central cap
selectors, their products remain in different direct summands.  The sector
decomposition theorem applies verbatim, proving the stated dichotomy.
