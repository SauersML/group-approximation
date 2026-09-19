---
rg: 2
id: centralizer-hnn-is-free-generalized-wreath
kind: claim
title: Every subgroup-centralizer HNN extension is a free generalized coset wreath product
distinct_from:
  sl2-centralizer-hnn-is-free-coset-wreath: that records the dyadic rank-one instance and its Bruhat--Tits interpretation; this is the group-theoretic theorem for an arbitrary inclusion and is consumed by the large-prime SL3 actor-covariance audit.
  arithmetic-double-swap-extension-is-binary-coset-wreath: that uses order-two lamps and packages the factor-swap extension of an amalgamated double; this uses infinite cyclic free lamps and identifies the centralizer HNN group itself.
---

**ESTABLISHED STRUCTURAL THEOREM.**  For every inclusion `C<=A`, put

```text
G=<A,t | [t,c]=1 for every c in C>,          X=A/C.
```

Then canonically

```text
G ~= ( *_(x in X) Z_x ) rtimes A
  = Z wr^*_(A curvearrowright X) A.                           (CGW1)
```

The base stable letter is the generator `z_C`, and

```text
a t a^(-1)  <->  z_(aC).                                    (CGW2)
```

Thus the quasiregular unitary frame of
`full-hnn-regularity-is-a-quasiregular-unitary-orbit` is not merely an
analogy: it is the canonical free-lamp basis of the exact group.  Retaining
the actor covariance which was absent from
`finite-lamp-frame-is-matrix-range-neutral` means retaining precisely the
free generalized wreath product over the coset action.

DERIVATION
centralizer-hnn-free-wreath-proof
