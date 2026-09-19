---
rg: 2
id: fix-bhmet-char-p-host-tree-word
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord: automatically included section variable(s) unused in theorem ..."
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeWord.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 3 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeWord.lean:82:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_one_apply`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeWord.lean:98:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.map_one_shift`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeWord.lean:119:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_mul`:
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-char-p-host-tree-word`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
