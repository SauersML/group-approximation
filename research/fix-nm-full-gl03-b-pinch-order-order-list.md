---
rg: 2
id: fix-nm-full-gl03-b-pinch-order-order-list
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderList: unexpected token '+'; expected term"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderList.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderList.lean:24:21: unexpected token '+'; expected term
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderList` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
