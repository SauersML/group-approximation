---
rg: 2
id: kl-length-six-four-sign-change-words-inject
kind: claim
title: Length-six words with four sign changes inject unless the same-sign quotient has finite order or absorbs a loop coefficient
invalidates: [leavitt-kl-violation-from-four-sign-change-length-six-words]
distinct_from:
  length-five-kl-fence-for-leavitt-equations: that protects every word of variable length at most five and lists the length-six sign classes left open; this settles two of those classes generically, over every coefficient group.
  leavitt-paired-quotient-passes-relative-weight-test: that applies the weight test to one paired Leavitt quotient of the class ++++--; this applies it to the relator itself for the two classes with four sign changes.
  kl-cyclic-cover-words-have-an-index-m-core: that presents the index-two core of the +++-+- words; this proves those words inject generically without using the core.
---

Let `G` be any group and `w in G * <t>` a cyclically reduced word of variable
length six in which every `t`-exponent is `+-1` and the cyclic sign pattern has
four sign changes.  Up to inversion and cyclic rotation these are exactly the
classes `+++-+-` and `++-++-`, both of degree two.  Suppose `w` is not a proper
power.  Write `x_1, ..., x_4` for the coefficients between opposite signs and
`y, y'` for the two coefficients between two positive letters.  If

```text
y^(-1) y'  has infinite order,  and  no x_i lies in <y y'^(-1)> or <y^(-1) y'>,
```

then the relative presentation `<G, t | w>` is aspherical, and
`G -> (G * <t>)/<<w>>` is injective.

In particular the conclusion holds whenever `y^(-1) y'` has infinite order and
all four `x_i` have finite order.  Elementary Leavitt roots are such involutions.

## Consequence for the Leavitt lane

A Kervaire--Laudenbach violation of length six over any group, in particular
over `R^x`, has sign class `++++--`, or it has four sign changes together with
a finite-order `y^(-1) y'` or a loop coefficient in one of the two cyclic
groups.  The window words `a_1 t b_1 t^(-1) a_2 t b_2 t^(-1) a_3 t b_3 t` of
`kl-cyclic-cover-words-have-an-index-m-core` are the class `+++-+-`, with
`y = b_3` and `y' = a_1`.
