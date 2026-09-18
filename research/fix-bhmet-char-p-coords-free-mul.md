---
rg: 2
id: fix-bhmet-char-p-coords-free-mul
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul: Unknown constant Localization.Away"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 6 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean:35:22: Unknown constant `Localization.Away`
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean:65:8: declaration uses `sorry`
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean:79:36: Invalid argument name `A` for function `awayMulLeft`
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean:93:14: Unknown constant `GroupApproximation.BooneHigman.Metabelian.CharPCoords.awayMulLeft_injective`
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-char-p-coords-free-mul`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
