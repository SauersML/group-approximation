---
rg: 2
id: fix-nm-full-gl03-b-pinch-order-split
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.Split: unexpected token '+'; expected term"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/Split.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/Split.lean:55:13: unexpected token '+'; expected term
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/Split.lean:167:57: unexpected token '+'; expected term
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/Split.lean:189:53: unexpected token '+'; expected term
error: GroupApproximation/Manuscript/NonMF/Full/GL03BPinchOrder/Split.lean:255:72: unexpected token '+'; expected term
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.Split` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
