---
rg: 2
id: fix-sk-full-lv-assembly-setup
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Setup: Unknown identifier GroupApproximation.BinaryLeavitt.BinaryLeavittAlgeb"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Setup.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Setup.lean:28:15: Unknown identifier `GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Setup.lean:31:41: Unknown identifier `BinL`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Setup.lean:34:42: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVAssembly/Setup.lean:34:30: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Setup` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
