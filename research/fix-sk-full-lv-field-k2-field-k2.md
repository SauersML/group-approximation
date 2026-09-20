---
rg: 2
id: fix-sk-full-lv-field-k2-field-k2
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2: Unknown constant Subgroup.closure_le.mpr"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/FieldK2.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/FieldK2.lean:59:45: Unknown constant `Subgroup.closure_le.mpr`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFieldK2/FieldK2.lean:60:2: No goals to be solved
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
