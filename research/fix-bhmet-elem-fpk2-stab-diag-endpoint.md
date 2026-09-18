---
rg: 2
id: fix-bhmet-elem-fpk2-stab-diag-endpoint
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint: 'change"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2StabDiagEndpoint.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 3 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2StabDiagEndpoint.lean:70:4: 'change
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2StabDiagEndpoint.lean:74:4: 'change ⁅stabDiagLeftPerm n R (x i j hij a), stabDiagLeftPerm n R (x k l hkl b)⁆ = 1' tactic does nothing
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2StabDiagEndpoint.lean:78:4: 'change
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-elem-fpk2-stab-diag-endpoint`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
