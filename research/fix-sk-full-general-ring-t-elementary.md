---
rg: 2
id: fix-sk-full-general-ring-t-elementary
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Elementary: Unknown constant Subgroup.map_closure"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Elementary.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Elementary.lean:177:8: Unknown constant `Subgroup.map_closure`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Elementary.lean:242:14: 'GroupApproximation.Full.SK03.closure_elementaryGenerators_eq_top' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/GeneralRingT/Elementary.lean:243:14: 'GroupApproximation.Full.SK03.elementaryGroup_fg' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Elementary` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
