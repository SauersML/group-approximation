---
rg: 2
id: fix-bh-palomar-graph-products-product-input
kind: claim
title: "Fix GroupApproximation.BHPalomar.GraphProducts.ProductInput: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BHPalomar/GraphProducts/ProductInput.lean` is red on main at 4067aaa686 (trusted batched probe, job direct-b1789912910). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-graphprod.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bh-palomar-graph-products-product-closure`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BHPalomar.GraphProducts.ProductInput` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
