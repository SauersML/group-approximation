---
rg: 2
id: fix-bhmet-envelope-higman-vc-tau-d2-residual
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Residual: Used tac1 <;> tac2 where (tac1; tac2) would suffice"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Residual.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Residual.lean:76:38: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Residual.lean:77:56: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Residual.lean:78:56: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauD2Residual.lean:79:56: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Residual` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
