---
rg: 2
id: magic-square-faces-present-a-fixed-extraspecial-packet
kind: claim
title: Homogeneous Magic-Square faces present a fixed extraspecial packet
distinct_from:
  s3-cannot-be-a-homogeneous-parity-face-factor: that rules out S3 from its sparse involution commuting geometry; this gives a positive fixed-packet example.
---

# Homogeneous Magic-Square faces present a fixed extraspecial packet

ESTABLISHED.

The finite nonabelian packet in the proposed `K x F_2^r` construction is not
itself an obstruction. Take nine involutions in a three-by-three square,
require commutation and product one on every row and on the first two columns,
and require product `J` on the last column, where `J` is a central involution.
Equivalently, include `J` in the last face so every face is homogeneous.

The resulting universal group is the two-qubit real Pauli group, equivalently
the central product of two copies of `D_8`; it has order `32`, center `<J>`,
and is extraspecial.

Eliminate the last entry of every row and the bottom entries of the first two
columns. Four involutions `a,b,d,e` remain, with every cross pair between
`{a,e}` and `{b,d}` commuting except `(a,e)` and `(b,d)`. Before the final
two face constraints this is `D_infinity x D_infinity`. Those constraints
identify

```text
u=(ae)^2=[a,e],   v=(bd)^2=[b,d]
```

and force `u=v=u^{-1}`. Since the dihedral factors commute, the common
element is central and has order two. The last-column product is `(ae)^2`,
so it identifies this element with `J`. Collection gives at most the `32`
normal forms

```text
J^epsilon a^alpha e^eta b^beta d^delta.
```

The standard two-qubit Pauli matrices realize all `32`, proving that there is
no further collapse.

Thus bounded homogeneous faces can supply a fixed finite packet with a
uniform finite-dimensional conjugation gap. The genuine obstruction is
coupling a positive-rate growing code factor without leaving a larger
universal completion.

## Consequence

This supplies the fixed-`K` half of
`finite-k-commuting-face-universal-completion`, but not the claimed direct
product with the logical code bits.
