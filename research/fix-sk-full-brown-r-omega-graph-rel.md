---
rg: 2
id: fix-sk-full-brown-r-omega-graph-rel
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.GraphRel: Unknown identifier h1"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/BrownROmega/GraphRel.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/BrownROmega/GraphRel.lean:85:36: Unknown identifier `h1`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/BrownROmega/GraphRel.lean:85:9: Tactic `rcases` failed: `x✝ : ?m.149` is not an inductive datatype
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/BrownROmega/GraphRel.lean:203:36: Unknown identifier `h`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/BrownROmega/GraphRel.lean:203:9: Tactic `rcases` failed: `x✝ : ?m.138` is not an inductive datatype
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.GraphRel` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
