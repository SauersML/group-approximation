---
rg: 2
id: fix-bhmet-absorption-suslin-euclid-kill
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill: Type mismatch"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean:108:12: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean:109:12: Type mismatch
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-absorption-suslin-euclid-kill`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
