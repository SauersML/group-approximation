---
rg: 2
id: fix-sk-full-a2-local-lifting-property
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Property: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/Property.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/Property.lean:94:10: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/Property.lean:95:77: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/A2LocalLifting/Property.lean:190:14: 'GroupApproximation.Full.A2LocalLifting.OperatorSystemMatrixArvesonStatement' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Property` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
