---
rg: 2
id: fix-nm-full-involution-blocks-return-section
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.InvolutionBlocks.ReturnSection: failed to synthesize instance of type class"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/InvolutionBlocks/ReturnSection.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/InvolutionBlocks/ReturnSection.lean:50:6: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/NonMF/Full/InvolutionBlocks/ReturnSection.lean:68:6: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/NonMF/Full/InvolutionBlocks/ReturnSection.lean:249:6: Type mismatch
error: GroupApproximation/Manuscript/NonMF/Full/InvolutionBlocks/ReturnSection.lean:252:39: Application type mismatch: The argument
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.InvolutionBlocks.ReturnSection` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
