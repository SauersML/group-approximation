---
rg: 2
id: fix-bh-palomar-graph-products-envelope-split
kind: claim
title: "Fix GroupApproximation.BHPalomar.GraphProducts.EnvelopeSplit: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BHPalomar/GraphProducts/EnvelopeSplit.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bh-palomar-graph-products-product-closure`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BHPalomar.GraphProducts.EnvelopeSplit` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
