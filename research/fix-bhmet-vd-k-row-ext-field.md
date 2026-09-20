---
rg: 2
id: fix-bhmet-vd-k-row-ext-field
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.VdKRowExtField: Variable name N is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/VdKRowExtField.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789910605 on main 516e496a4a).**

```
error: GroupApproximation/BooneHigman/Metabelian/VdKRowExtField.lean:54:78: Variable name `N` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.VdKRowExtField` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
