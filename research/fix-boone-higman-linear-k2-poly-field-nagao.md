---
rg: 2
id: fix-boone-higman-linear-k2-poly-field-nagao
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.FieldNagao: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/FieldNagao.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**Repair landed, unprobed.** f47b0a3483: K2 program: FieldNagao subgroup defs noncomputable (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-sk-leavitt-k2-padded-central-matrix-id`, `fix-sk-sk-rows-steinberg-weyl-diagonal`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.FieldNagao` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
