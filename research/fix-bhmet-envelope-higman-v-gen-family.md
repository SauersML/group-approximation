---
rg: 2
id: fix-bhmet-envelope-higman-v-gen-family
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily: Unknown constant Subgroup.closure"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 6 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean:79:6: Unknown constant `Subgroup.closure`
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean:80:26: Unknown constant `Subgroup.closure`
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean:84:10: Unknown constant `Subgroup.mem_map.mpr`
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean:87:25: Unknown constant `Subgroup.mem_map.mp`
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-envelope-higman-v-gen-family`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
