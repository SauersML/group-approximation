---
rg: 2
id: fix-boone-higman-linear-k2-poly-field-nf-weyl-check
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylCheck: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/FieldNF/WeylCheck.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bhmet-elem-fpk2-poly-deg-spans`, `fix-bhmet-elem-fpk2-surj-stab-vec`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylCheck` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
