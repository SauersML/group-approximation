---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-rel-pres-iso
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresIso: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresIso.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```


**Inputs (nearest red imports).** `fix-boone-higman-linear-char-zero-k2-found-rel-pres-act`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresIso` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
