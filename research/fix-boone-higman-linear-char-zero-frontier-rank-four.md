---
rg: 2
id: fix-boone-higman-linear-char-zero-frontier-rank-four
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.FrontierRankFour: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/FrontierRankFour.lean` is red on main at 4067aaa686 (trusted batched probe, job direct-b1789912910). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bhmet-char-zero-coords-assembly`, `fix-bhmet-elem-fp-char-zero-k2-fng-endpoint`, `fix-bhmet-elem-fp-char-zero-tri-off-lift`, `fix-bhmet-elem-fp-char-zero-tri-off-vec`, `fix-bhmet-elem-fpk2-surj-stab-gauss-euclid`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.FrontierRankFour` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
