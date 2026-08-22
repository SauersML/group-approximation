---
rg: 2
id: leavitt-revised-degree4-injectivity-proof
kind: route
title: Intersect a hypothetical kernel disk with the preserved V4 and D8 gate factors
target: leavitt-revised-degree4-candidate-is-injective
requires:
  - leavitt-degree-four-corner-subgroup-is-v4-d8-f4
  - leavitt-degree4-abstract-tietze-preserves-d
---

Let `C=G_0*G_1*G_2*G_3` be the coefficient group in the index-four
Reidemeister--Schreier presentation, and let

```text
Q=V4(a0,b0)*D8(c3,d3)*F(H,K,L,M) -> C               (GI1)
```

be the injective corner map.  The Nielsen proof gives more than injectivity.
A reduced `Q` word containing a long letter expands to at least two `C`
syllables; a reduced word alternating the two finite gate factors also has at
least two syllables unless it lies in one factor.  Therefore

```text
Q intersect G0 = V4(a0,b0),
Q intersect G3 = D8(c3,d3),
Q intersect G1 = Q intersect G2 = 1.                 (GI2)
```

Suppose a nonidentity `g in G_i` dies in the full relative quotient.  Choose
a relative picture for `g` over the four orbit relators.  Every stable-letter
corner is one of the eight generators of `Q`.  Each inner coefficient region
therefore reads a word in `Q` which is the identity in `C`.  Injectivity in
`(GI1)` says it is already the identity in abstract `Q`; equivalently, the
same labelled picture is a picture over the abstract corner presentation

```text
P=<Q,z | H z, z b z^(-1)d z L,
             z a z^(-1)c z M, z K>.                  (GI3)
```

On the outer region, the coefficient corners multiply with `g` to the
identity in `C`.  Hence `g` equals an element of `Q`, so `(GI2)` puts it in
the corresponding finite gate factor (or makes it trivial immediately for
`i=1,2`).  The abstract picture `(GI3)` also says this element lies in the
kernel of `Q -> P`.

But Tietze elimination identifies

```text
P=(V4*D8)*<H>
```

and `Q -> P` is injective on `V4*D8`.  Thus its kernel meets every group in
`(GI2)` trivially, contradicting `g !=1`.  All four maps `G_i` into the
index-four quotient are injective.

Finally, the exponent sum of `W'` is four.  The original relative quotient
maps to `Z/4` by `t -> 1` and `G -> 0`; its kernel is exactly the
Reidemeister--Schreier quotient used above, with the original coefficient copy
equal to `G_0`.  Injectivity of `G_0` in the kernel proves coefficient
injectivity in the original one-relator extension.
