---
rg: 2
id: fix-boone-higman-linear-char-p-low-trdeg-coords
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCoords: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-charp.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean:58:33: failed to synthesize instance of type class
error: GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean:58:9: Tactic `rcases` failed: `x✝ : ?m.159` is not an inductive datatype
error: GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean:79:14: 'GroupApproximation.BooneHigmanLinear.CharP.exists_polynomialCoordinates_le_trdeg' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/CharP/LowTrdegCoords.lean:91:14: 'GroupApproximation.BooneHigmanLinear.CharP.exists_polynomialCoordinates_le_one' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCoords` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
