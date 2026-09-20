---
rg: 2
id: fix-sk-full-lv-skew-laurent-k2-units
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Units: Unknown constant MulEquiv.piUnits"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Units.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Units.lean:59:5: Unknown constant `MulEquiv.piUnits`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Units.lean:61:0: Not a definitional equality: the left-hand side
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Units.lean:65:2: Type mismatch
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Units.lean:71:24: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Units` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
