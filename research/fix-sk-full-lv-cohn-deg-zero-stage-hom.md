---
rg: 2
id: fix-sk-full-lv-cohn-deg-zero-stage-hom
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.StageHom: Variable name x is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnDegZero/StageHom.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**Repair landed, unprobed.** 132466a3a3: SK Full/LV*: static repairs of 9 root-imported red modules (from union build b1789878900; . Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnDegZero/StageHom.lean:74:9: Variable name `x` is not explicitly referenced.
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnDegZero/StageHom.lean:74:11: Variable name `y` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.StageHom` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
