---
rg: 2
id: wreath-finiteness-transfers-from-product-closed-classes
kind: claim
title: The marked-site tensor proof transfers finiteness from any subgroup-and-product-closed class
distinct_from:
  rf-lamp-permutational-wreaths-satisfy-stable-finiteness: that starts with residually finite lamp and base groups; this isolates the exact algebraic closure hypotheses and permits already nonsofic groups as inputs.
  split-local-corner-extensions-preserve-stable-finiteness: that is a ring extension lemma; this builds separating representations of a wreath group algebra using an entire class of coefficient group algebras.
---

Fix a field k. Let C be a class of groups containing the trivial group,
closed under subgroups and finite direct products, and such that k[H]
is stably finite for every H in C. Then, for A,G in C and any G-set X,

    k[A wr_X G]

is stably finite. The wreath product is restricted and the action only
permutes lamp factors. Neither residual finiteness nor a finite model of
the action is needed beyond the stated class hypotheses.

The hypothesis is about all group algebras of the product-closed class.
It is not enough to know only that k[A] and k[G] are stably finite;
the proof also needs coefficient rings coming from finite mixed products
of A, G, and stabilizers. No general tensor-product permanence theorem for
stably finite rings is asserted.

`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` isolates a
sharper sufficient hypothesis using a diagonal crossed-product induction:
it suffices that k[A^j x H] is stably finite for all finite j and H<=G.
Residual finiteness of A and stable finiteness of k[G] alone verify
this condition. For more general lamps this remains a hypothesis on
the mixed coefficient algebras, not an inference from separate stable
finiteness of k[A] and k[G].
