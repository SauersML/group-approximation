---
rg: 2
id: fix-sk-full-lv-skew-laurent-k2-interface
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface: failed to compile definition, consider marking it as 'noncomputable' b"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Interface.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Interface.lean:57:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'SkewMonoidAlgebra.singleOneRingHom', which is 'non
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Interface.lean:62:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'SkewMonoidAlgebra.single', which is 'noncomputable
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Interface.lean:68:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'SkewMonoidAlgebra.instNonAssocRing', which is 'non
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVSkewLaurentK2/Interface.lean:80:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'SkewMonoidAlgebra.instNonAssocSemiring', which is 
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
