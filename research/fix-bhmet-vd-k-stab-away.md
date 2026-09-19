---
rg: 2
id: fix-bhmet-vd-k-stab-away
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.VdKStabAway: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/VdKStabAway.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```


**Inputs (nearest red imports).** `fix-stable-range-instances`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.VdKStabAway` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
