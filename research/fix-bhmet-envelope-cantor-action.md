---
rg: 2
id: fix-bhmet-envelope-cantor-action
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeCantorAction.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeCantorAction.lean:75:60: unsolved goals
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-envelope-cantor-action`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
