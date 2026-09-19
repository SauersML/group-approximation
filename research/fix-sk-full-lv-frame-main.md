---
rg: 2
id: fix-sk-full-lv-frame-main
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Main: Expected type must not contain free variables"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFrame/Main.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFrame/Main.lean:57:30: Expected type must not contain free variables
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFrame/Main.lean:59:14: 'GroupApproximation.Full.LVFrame.vertex_of_isFrame' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFrame/Main.lean:63:31: Expected type must not contain free variables
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVFrame/Main.lean:63:51: Expected type must not contain free variables
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Main` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
