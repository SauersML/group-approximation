---
rg: 2
id: fix-bhmet-torsion-free-coprimary-block
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock: expected token"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/TorsionFreeCoprimaryBlock.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 5 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeCoprimaryBlock.lean:33:53: expected token
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeCoprimaryBlock.lean:57:68: expected token
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeCoprimaryBlock.lean:57:38: typeclass instance problem is stuck
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeCoprimaryBlock.lean:104:65: expected token
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-torsion-free-coprimary-block`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
