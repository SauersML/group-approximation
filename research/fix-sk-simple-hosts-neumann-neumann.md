---
rg: 2
id: fix-sk-simple-hosts-neumann-neumann
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann: This simp argument is unused:"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/NeumannNeumann.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/NeumannNeumann.lean:151:48: This simp argument is unused:
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
