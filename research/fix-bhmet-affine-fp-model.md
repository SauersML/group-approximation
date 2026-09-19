---
rg: 2
id: fix-bhmet-affine-fp-model
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.AffineFPModel: Type mismatch"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 8 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean:132:62: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean:135:14: Unknown constant `GroupApproximation.BooneHigman.Metabelian.AffineFP.model_conj_single`
error: GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean:140:12: Unknown identifier `model_conj_single`
error: GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean:139:86: unsolved goals
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-affine-fp-model`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AffineFPModel` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
