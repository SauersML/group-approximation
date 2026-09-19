---
rg: 2
id: fix-bhmet-char-p-coords-free-mul
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul: Unknown constant Localization.Away"
---

**RESOLVED (2d6ebaf55).** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPCoordsFreeMul.lean` failed to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 6 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. It was OPEN until a trusted probe built it green; see below.

**Green.** Built green (lake ✔ or replay) by the trusted gqprobe-lean v4 batch, Slurm job 1328760 (request log gq-slurm/batch-b1789769423-3.log, lane bh-pal-wire). That build used base d2df12ed9 plus the overlay later landed as 2d6ebaf55, and no other overlay was in the batch. The job was cancelled after these modules had compiled. Since then no file in this module's import closure has changed on main, only downstream modules and a lakefile comment. That cancellation is why the index loop, which requires a completed batch, did not record it.

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
