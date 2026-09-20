---
rg: 2
id: fix-bhmet-char-zero-coords-assembly
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsAssembly.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsAssembly.lean:62:38: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsAssembly.lean:66:14: 'GroupApproximation.BooneHigman.Metabelian.CharZeroHost.fgSubringCoordinates' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsAssembly.lean:74:2: 'GroupApproximation.BooneHigman.Metabelian.CharZeroHost.charZeroPolynomialCoordinates' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
