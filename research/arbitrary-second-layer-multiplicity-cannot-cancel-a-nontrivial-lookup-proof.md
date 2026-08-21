---
rg: 2
id: arbitrary-second-layer-multiplicity-cannot-cancel-a-nontrivial-lookup-proof
kind: route
title: Evaluate the proposed cancellation in a faithful representation of the free product
target: arbitrary-second-layer-multiplicity-cannot-cancel-a-nontrivial-lookup
requires: []
---

Regard the word as an element `bar_w` of the free product `K*<t>`.  Apply
`(SLN2)` to a faithful unitary representation of `K*<t>` (for example its
left regular representation), taking `V` to be the image of `t` and `sigma`
the restriction to `K`.  Faithfulness gives

```text
bar_w=1 in K*<t>.                                      (SLP1)
```

The homomorphism `K*<t> -> K` which is the identity on `K` and sends `t` to
`a` therefore sends `bar_w` to `1`.  This contradicts `(SLN1)`, where its
image is `z!=1`.

For tensor-product packet actions the separation is literal: evaluation of
the word on `k -> pi(k) tensor sigma(k)` and
`t -> pi(a) tensor V` is the tensor product of the two word evaluations.
Thus a nontrivial finite truth output cannot be protected from a completely
arbitrary second-layer action by balancing, commutator nesting, or a longer
word; some additional relation or type selection is mathematically
necessary.

