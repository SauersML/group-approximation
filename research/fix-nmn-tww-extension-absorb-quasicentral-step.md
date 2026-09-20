---
rg: 2
id: fix-nmn-tww-extension-absorb-quasicentral-step
kind: route
title: "Fix GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbQuasicentralStep: root-imported and red on main"
status: OPEN
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMFNotes/Full/TWWSchafhauser/ExtensionAbsorbQuasicentralStep.lean` is red on main at 37ed9e00e (trusted batched probe, direct-b1789878900, found by the ms-map root probe). It IS imported by the root `GroupApproximation.lean`, so the root build is red while it is. Owner: ms-map (root wiring).

**First error (verbatim).**

```
error: GroupApproximation/Manuscript/NonMFNotes/Full/TWWSchafhauser/ExtensionAbsorbQuasicentralStep.lean:98:0: automatically included section variable(s) unused in theorem `GroupApproximation.Full.TWWSchafhauser.quasiUnit_map_real_smul`:
  [PartialOrder A]
  [StarOrderedRing A]
(the same at 102:0 for quasiUnit_defect_mem)
```

**What it needs.** Add `omit [PartialOrder A] [StarOrderedRing A] in` before the two theorems (the linter's own suggestion; statements unchanged).

**Resolution.** Fix landed by ms-map; when a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
