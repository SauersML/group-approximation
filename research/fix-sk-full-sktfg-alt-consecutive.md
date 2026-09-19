---
rg: 2
id: fix-sk-full-sktfg-alt-consecutive
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.AltConsecutive: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/AltConsecutive.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/AltConsecutive.lean:80:2: Type mismatch
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/AltConsecutive.lean:89:56: Unknown identifier `mclosure_swap_castSucc_succ`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/AltConsecutive.lean:91:13: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/AltConsecutive.lean:159:14: 'GroupApproximation.Full.SKTFG.alternatingGroup_le_closure_consSet' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.AltConsecutive` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
