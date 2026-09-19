---
rg: 2
id: fix-bhmet-coprimary-module
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CoprimaryModule: failed to compile definition, consider marking it as 'noncomputable' ..."
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CoprimaryModule.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CoprimaryModule.lean:133:9: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'MonoidAlgebra.semiring', which is 'noncomputable'
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-coprimary-module`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CoprimaryModule` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
