---
rg: 2
id: fix-boone-higman-linear-panin-affine-cor29
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-boone-higman-linear-tulenbaev-horrocks-statements`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
