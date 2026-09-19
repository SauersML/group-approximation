---
rg: 2
id: fix-boone-higman-linear-k2-poly-symbol-central
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.SymbolCentral: This simp argument is unused:"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/SymbolCentral.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/K2Poly/SymbolCentral.lean:107:36: This simp argument is unused:
error: GroupApproximation/BooneHigmanLinear/K2Poly/SymbolCentral.lean:113:39: This simp argument is unused:
error: GroupApproximation/BooneHigmanLinear/K2Poly/SymbolCentral.lean:120:39: This simp argument is unused:
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.SymbolCentral` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
