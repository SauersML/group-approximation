---
rg: 2
id: fix-boone-higman-linear-char-zero-leaves
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.Leaves: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/Leaves.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bhmet-char-zero-coords-assembly`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.Leaves` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
