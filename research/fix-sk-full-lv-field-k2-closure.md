---
rg: 2
id: fix-sk-full-lv-field-k2-closure
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.Closure: Unknown constant Subgroup.closure_le.mpr"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/Closure.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/Closure.lean:131:9: Unknown constant `Subgroup.closure_le.mpr`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/Closure.lean:132:2: No goals to be solved
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.Closure` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
