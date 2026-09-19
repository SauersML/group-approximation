---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-diagonal
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.Diagonal: automatically included section variable(s) unused in theorem GroupAppr"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/Diagonal.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Diagonal.lean:35:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.dgCoeff_add`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Diagonal.lean:42:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.dgCoeff_mul`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Diagonal.lean:55:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.dgCoeff_one`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Diagonal.lean:60:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.dgCoeff_dgCoeff`:
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.Diagonal` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
