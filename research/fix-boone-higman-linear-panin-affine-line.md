---
rg: 2
id: fix-boone-higman-linear-panin-affine-line
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Line: Polynomial.finset_sum_coeff has been deprecated: Use Polynomial.finset"
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Line.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Line.lean:55:28: `Polynomial.finset_sum_coeff` has been deprecated: Use `Polynomial.finsetSum_coeff` instead
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Line.lean:123:4: try 'simp' instead of 'simpa'
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Line.lean:130:73: typeclass instance problem is stuck
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Line.lean:161:4: This simp argument is unused:
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Line` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
