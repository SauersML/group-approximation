---
rg: 2
id: fix-sk-full-stepanov-matui-matui-tower-coords
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerCoords: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiTowerCoords.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.

**Repair landed, unprobed.** 1942e6f93a: SK: fix three red root-closure modules (MatuiTowerCoords, LamplighterWP.Reduction, MatuiRo. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiTowerCoords.lean:117:45: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiTowerCoords.lean:117:39: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiTowerCoords.lean:118:13: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/StepanovMatui/MatuiTowerCoords.lean:118:7: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerCoords` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
