---
rg: 2
id: fix-sk-sk-open-hyperbolic-host
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.HyperbolicHost: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/HyperbolicHost.lean` is red on main at 463f140e0d (trusted batched probe, Slurm job 1398755). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-sk-open.


**Repair landed, unprobed.** 3c57ee4c3b: SK SkOpen/HyperbolicHost: route clause (b) of fc84c012b409 through the current NM open sta. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-sk-simple-hosts-host`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.HyperbolicHost` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
