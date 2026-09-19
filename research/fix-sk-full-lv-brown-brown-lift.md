---
rg: 2
id: fix-sk-full-lv-brown-brown-lift
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownLift: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVBrown/BrownLift.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVBrown/BrownLift.lean:93:32: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVBrown/BrownLift.lean:115:65: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVBrown/BrownLift.lean:134:14: 'GroupApproximation.Full.LVBrown.brown_lift' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownLift` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
