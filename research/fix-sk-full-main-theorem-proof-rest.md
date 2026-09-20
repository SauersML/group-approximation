---
rg: 2
id: fix-sk-full-main-theorem-proof-rest
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofRest: Ambiguous term"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofRest.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofRest.lean:220:20: Ambiguous term
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofRest.lean:220:8: Type mismatch: After simplification, term
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofRest.lean:264:14: 'GroupApproximation.Full.SK05.rest_models' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofRest.lean:266:21: 'GroupApproximation.Full.SK05.printedMainProofRest' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofRest` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
