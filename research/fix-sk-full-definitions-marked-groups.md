---
rg: 2
id: fix-sk-full-definitions-marked-groups
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.MarkedGroups: unexpected identifier; expected '}'"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/MarkedGroups.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/MarkedGroups.lean:130:82: unexpected identifier; expected '}'
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/MarkedGroups.lean:130:10: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Exists.intro` has 2 explicit field, but only 1 was provided
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/MarkedGroups.lean:130:11: Fields missing: `decidableEq`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/MarkedGroups.lean:126:40: unsolved goals
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.MarkedGroups` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
