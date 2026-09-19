---
rg: 2
id: fix-bhmet-affine-fp-model
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.AffineFPModel: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/AffineFPModel.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 8 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. Stays OPEN until a trusted probe builds it green.

**Still red after wave 1** (batch job 1328760, base d2df12ed9). A second repair landed at 55aba370a, unprobed: MSI Slurm submission is blocked. It stays OPEN until a trusted probe builds it green.

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
