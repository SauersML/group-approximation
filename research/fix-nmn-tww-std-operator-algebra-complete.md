---
rg: 2
id: fix-nmn-tww-std-operator-algebra-complete
kind: route
title: "Fix GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraComplete: root-imported and red on main"
status: OPEN
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMFNotes/Full/TWWSchafhauser/StdOperatorAlgebraComplete.lean` is red on main at 37ed9e00e (trusted batched probe, direct-b1789878900, found by the ms-map root probe). It IS imported by the root `GroupApproximation.lean`, so the root build is red while it is. Owner: ms-map (root wiring).

**First error (verbatim).**

```
error: GroupApproximation/Manuscript/NonMFNotes/Full/TWWSchafhauser/StdOperatorAlgebraComplete.lean:124:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  inner ?m.350 ?m.363 (?m.364 - ?m.365)
```

**What it needs.** Rewrite with the repository's own CStarModule lemmas, (standardModule ℕ J).inner_sub_right and inner_sub_left. Under `open GroupApproximation.HilbertModule`, the bare names CStarModule.inner_sub_right and inner_sub_left resolve to Mathlib's lemmas, whose pattern is Mathlib's inner.

**Resolution.** Fix landed by ms-map; when a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
