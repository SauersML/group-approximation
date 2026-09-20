---
rg: 2
id: fix-sk-full-a2-local-lifting-trace-vanishing
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.TraceVanishing: advertised closed endpoint 'GroupApproximation.Full.A2LocalLifting.has"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/TraceVanishing.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/TraceVanishing.lean:309:21: advertised closed endpoint 'GroupApproximation.Full.A2LocalLifting.hasTracePreservingMatrixModel_of_isHyperlinear' has a leading input; 
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.TraceVanishing` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
