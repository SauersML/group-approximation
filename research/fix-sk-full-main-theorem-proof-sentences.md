---
rg: 2
id: fix-sk-full-main-theorem-proof-sentences
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences: Function expected at"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofSentences.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofSentences.lean:161:49: Function expected at
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofSentences.lean:252:50: Unknown identifier `TotallyDisconnectedSpace`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofSentences.lean:265:9: don't know how to synthesize implicit argument `TotallyDisconnectedSpace`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/MainTheorem/ProofSentences.lean:265:9: don't know how to synthesize implicit argument
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
