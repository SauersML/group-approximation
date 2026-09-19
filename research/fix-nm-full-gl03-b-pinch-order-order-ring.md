---
rg: 2
id: fix-nm-full-gl03-b-pinch-order-order-ring
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderRing: Application type mismatch: The argument"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderRing.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderRing.lean:96:24: Application type mismatch: The argument
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderRing.lean:120:35: unexpected token ':='; expected ')', ',' or ':'
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderRing.lean:105:88: unsolved goals
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/OrderRing.lean:141:14: 'GroupApproximation.Full.GL03BPinchOrder.ordRing_facePerm_val_of_getElem' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderRing` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
