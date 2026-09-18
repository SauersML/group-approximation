---
rg: 2
id: fix-bhmet-char-p-host-carry-recursion
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPHost.CarryRecursion: automatically included section variable(s) unused in theorem ..."
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPHost/CarryRecursion.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/CarryRecursion.lean:99:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.carryDigits_nil`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/CarryRecursion.lean:101:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.carryDigits_cons`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/CarryRecursion.lean:125:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.listPoint_nil`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/CarryRecursion.lean:127:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.listPoint_cons`:
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-char-p-host-carry-recursion`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharPHost.CarryRecursion` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
