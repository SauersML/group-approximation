---
rg: 2
id: fix-sk-full-general-ring-t-ring
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Ring: Unknown identifier ZMod"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Ring.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Ring.lean:37:42: Unknown identifier `ZMod`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Ring.lean:38:51: Unknown identifier `ZMod`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Ring.lean:39:58: Unknown identifier `ZMod`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Ring.lean:41:43: Unknown identifier `ZMod`
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Ring` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
