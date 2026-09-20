---
rg: 2
id: fix-bh-palomar-graph-products-product-closure
kind: claim
title: "Fix GroupApproximation.BHPalomar.GraphProducts.ProductClosure: Definition GroupApproximation.BHPalomar.GraphProducts.sumProdAction of"
---

**OPEN.** Lean module `GroupApproximation/BHPalomar/GraphProducts/ProductClosure.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-graphprod.

**First errors (verbatim).**

```
error: GroupApproximation/BHPalomar/GraphProducts/ProductClosure.lean:117:0: Definition `GroupApproximation.BHPalomar.GraphProducts.sumProdAction` of class type must be marked with `@[reducible]` or `@[implicit_reducible]`
error: GroupApproximation/BHPalomar/GraphProducts/ProductClosure.lean:129:17: instance `GroupApproximation.BHPalomar.GraphProducts.sumProdAction` must be marked with `@[reducible]` or `@[implicit_reducible]`
```

**What it needs.** Make `GroupApproximation.BHPalomar.GraphProducts.ProductClosure` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
