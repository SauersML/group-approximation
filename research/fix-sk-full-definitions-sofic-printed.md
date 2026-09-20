---
rg: 2
id: fix-sk-full-definitions-sofic-printed
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted: unexpected identifier; expected '}'"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/SoficPrinted.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/SoficPrinted.lean:128:75: unexpected identifier; expected '}'
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/SoficPrinted.lean:128:9: Fields missing: `separated`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/Definitions/SoficPrinted.lean:175:14: 'GroupApproximation.Full.SK01.printedIsSofic_iff' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
