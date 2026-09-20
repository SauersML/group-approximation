---
rg: 2
id: fix-sk-full-lv-cohn-rel-k1-corner
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Corner: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnRelK1/Corner.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**Repair landed, unprobed.** 132466a3a3: SK Full/LV*: static repairs of 9 root-imported red modules (from union build b1789878900; . Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnRelK1/Corner.lean:29:0: automatically included section variable(s) unused in theorem `GroupApproximation.Full.LVCohnRelK1.unitSum_zero`:
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVCohnRelK1/Corner.lean:32:0: automatically included section variable(s) unused in theorem `GroupApproximation.Full.LVCohnRelK1.unitSum_add`:
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Corner` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
