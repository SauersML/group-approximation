---
rg: 2
id: paired-selflessness-witnesses-do-not-tensor
kind: claim
title: Paired ordinary-selflessness witnesses never tensor to a selflessness witness
distinct_from:
  complete-selflessness-tensor-permanence: that positive theorem uses complete selflessness or exactness to construct a different witness; this result rules out only the naive pairing of two ordinary free-product splittings.
  complete-graph-products-selfless-anchor: that theorem absorbs all other factors from one completely selfless anchor; this obstruction explains why replacing that anchor by two merely selfless factors is not formal.
---

Let `(A,tau)` and `(B,sigma)` be nontrivial tracial C-star probability
spaces with faithful GNS representations. Write `A_0,A_1` for the two
canonical free copies of `A` in `(A,tau)*(A,tau)`, and similarly write
`B_0,B_1`. Inside

```text
((A,tau)*(A,tau)) tensor_min ((B,sigma)*(B,sigma)),
```

pair the copies by putting `D_i=A_i tensor_min B_i`. Then `D_0` and
`D_1` are not free for the product trace.

In fact, for any nonzero centered `a in A` and `b in B`, the four
alternating centered elements

```text
a_0 tensor 1,  1 tensor b_1,  a_0* tensor 1,  1 tensor b_1*
```

have joint moment

```text
tau(a a*) sigma(b b*) > 0.
```

Consequently, tensoring or synchronizing two ordinary selflessness
splittings cannot itself prove that `A tensor_min B` is selfless. This is
an obstruction to that proof strategy, not a counterexample to tensor
permanence and not a claim that `A tensor_min B` is nonselfless.
