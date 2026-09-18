---
rg: 2
id: fix-bhmet-affine-fp-identities
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.AffineFPIdentities: Invalid field map: The environment does not contain Eq.map, so it is ..."
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/AffineFPIdentities.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AffineFPIdentities.lean:55:15: Invalid field `map`: The environment does not contain `Eq.map`, so it is not possible to project the field `map` from an expression
error: GroupApproximation/BooneHigman/Metabelian/AffineFPIdentities.lean:73:16: Invalid field `map`: The environment does not contain `Eq.map`, so it is not possible to project the field `map` from an expression
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-affine-fp-identities`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AffineFPIdentities` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
