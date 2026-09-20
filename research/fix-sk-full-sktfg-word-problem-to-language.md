---
rg: 2
id: fix-sk-full-sktfg-word-problem-to-language
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.WordProblemToLanguage: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/WordProblemToLanguage.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/WordProblemToLanguage.lean:127:80: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/WordProblemToLanguage.lean:136:12: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/WordProblemToLanguage.lean:175:11: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/WordProblemToLanguage.lean:177:14: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.WordProblemToLanguage` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
