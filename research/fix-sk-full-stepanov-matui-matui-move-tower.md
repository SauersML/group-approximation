---
rg: 2
id: fix-sk-full-stepanov-matui-matui-move-tower
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiMoveTower: failed to synthesize instance of type class"
---

**RESOLVED (9add2d485e, trusted batched probe job direct-b1789839564).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiMoveTower.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.

**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiMoveTower.lean:34:35: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiMoveTower.lean:37:34: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiMoveTower.lean:41:2: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiMoveTower.lean:42:4: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiMoveTower` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
