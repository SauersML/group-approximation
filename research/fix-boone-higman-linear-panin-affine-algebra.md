---
rg: 2
id: fix-boone-higman-linear-panin-affine-algebra
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Algebra: Unknown identifier Basis.ofVectorSpace"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Algebra.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Algebra.lean:70:11: Unknown identifier `Basis.ofVectorSpace`
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Algebra.lean:68:76: unsolved goals
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Algebra.lean:104:14: 'GroupApproximation.BooneHigmanLinear.PaninAffine.map_dvd_of_forall_dvd_coeffMap' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Algebra.lean:133:8: Unknown identifier `isUnit_of_mul_eq_one`
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Algebra` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
