---
rg: 2
id: fix-bhmet-envelope-higman-vc-tau-d2-class-ab
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassAB: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2ClassAB.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**Repair landed, unprobed.** ed7f648b07: BH chain wave 5: static fixes for bh-pal-wires reds in union build b1789839564 (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2ClassAB` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
