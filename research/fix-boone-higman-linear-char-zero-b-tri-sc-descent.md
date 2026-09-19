---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-sc-descent
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.SC.Descent: List.getLast?_eq_getLast has been deprecated: Use List.getLast?_eq_som"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/SC/Descent.lean` is red on main at eae37b23a2 (trusted batched probe, Slurm job direct-b1789842431). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/SC/Descent.lean:304:26: `List.getLast?_eq_getLast` has been deprecated: Use `List.getLast?_eq_some_getLast` instead
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.SC.Descent` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
