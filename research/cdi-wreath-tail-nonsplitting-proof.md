---
rg: 2
id: cdi-wreath-tail-nonsplitting-proof
kind: route
title: Reduce the special-decomposition tails modulo restricted functions and use abelianization
target: cdi-wreath-tail-cocycle-is-intrinsically-nonsplit
requires: []
---

Reduce the identity for `v_(b,c)` in `(CDI-C1)` modulo the normal subgroup
`F_3^(B)` of `F_3^B`.  Since `v_(b,c)` is restricted, its class is one, giving
`(CDI-C2)`.

Replacing a section lift of `b` by a restricted base element multiplies
`rho_b` by an element of `F_3^(B)`, so `q_b` is unchanged.  Conversely, if
all `q_b` are trivial, all tails are restricted.  The image of the special
embedding already contains the full restricted base.  Multiplying the lift
`(rho_b,b)` by `(rho_b^(-1),e)` then gives the pure lift `(1,b)`.  Pure lifts
and the restricted base generate the ordinary wreath product, proving

```text
all q_b=1  iff  G isomorphic_to F_3 wr B.               (CDI-C3)
```

But the abelianization of the regular wreath product has the coinvariant
quotient of its base:

```text
(direct_sum_B Z^3)_B = Z^3.
```

Hence `F_3 wr B` has infinite abelianization.  The CDI group `G` has property
`(T)`, so its abelianization is finite.  This contradicts `(CDI-C3)` and
proves the corona cocycle is nontrivial.

Finally CDI Proposition 3.8 sends `rho_b` to `pi^B(rho_b)` and uses
`eta(pi^B(rho_b))` in the product action.  Only restricted tuples have a
finite tensor unitary under `gamma`; the established nonzero corona class is
therefore exactly the obstruction to removing all tails by the section
changes available in the construction.

Primary source: Chifan--Drimbe--Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/abs/2205.07442),
Lemma 2.13, Corollary 2.15, and Proposition 3.8.

