---
rg: 2
id: fix-bhmet-envelope-higman-vc-tau-d2-words
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Words: Used tac1 <;> tac2 where (tac1; tac2) would suffice"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Words.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**Repair landed, unprobed.** ecfe76c3e3: BH chain wave 4: static fixes for the five bh-pal-wire reds of union build b1789837230 (un. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Words.lean:101:38: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Words.lean:124:56: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Words.lean:128:41: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Words` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
