---
rg: 2
id: fix-sk-full-fibonacci-model
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Fibonacci/Model.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Fibonacci/Model.lean:286:47: Type mismatch
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Fibonacci/Model.lean:315:21: 'GroupApproximation.Full.SK08.fibonacciDisplay' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
