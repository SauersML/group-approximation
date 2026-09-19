---
rg: 2
id: fix-bhmet-envelope-higman-vc-tau-d2-class-ob
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassOB: fails through red imports"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2ClassOB.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.


**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassOB` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
