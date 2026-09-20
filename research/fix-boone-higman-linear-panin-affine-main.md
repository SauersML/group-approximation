---
rg: 2
id: fix-boone-higman-linear-panin-affine-main
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Main: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Main.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.



**First errors (verbatim; from probe job direct-b1789910605 on main 516e496a4a).**

```
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Main.lean:52:18: This simp argument is unused:
```


**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Main` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
