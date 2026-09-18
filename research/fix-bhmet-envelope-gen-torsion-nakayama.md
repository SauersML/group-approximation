---
rg: 2
id: fix-bhmet-envelope-gen-torsion-nakayama
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama: Unknown constant Subgroup.map_closure"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeGenTorsionNakayama.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeGenTorsionNakayama.lean:61:8: Unknown constant `Subgroup.map_closure`
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeGenTorsionNakayama.lean:60:62: unsolved goals
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-envelope-gen-torsion-nakayama`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsionNakayama` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
