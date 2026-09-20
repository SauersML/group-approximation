---
rg: 2
id: fix-kourovka2175-main
kind: claim
title: "Fix GroupApproximation.Kourovka2175.Main: fails through red imports"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Kourovka2175/Main.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**What it needs.** Make `GroupApproximation.Kourovka2175.Main` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
