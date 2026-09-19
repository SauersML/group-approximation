---
rg: 2
id: fix-sk-full-sktfg-cylinders
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Cylinders: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Cylinders.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: fix-bh-b.


**Repair landed, unprobed.** 25942699a4: SKTFG: beta-reduce cylinder hypotheses and replace no-op congr steps (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim; from probe job direct-b1789850259 on main 13d4765e1b).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Cylinders.lean:54:4: 'congr 1' tactic does nothing
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Cylinders.lean:59:4: 'congr 1' tactic does nothing
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Cylinders.lean:210:48: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Cylinders.lean:295:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```


**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Cylinders` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
