---
rg: 2
id: fix-bhmet-char-zero-host-letters
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters: failed to compile definition, consider marking it as 'noncomputable' ..."
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean:60:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.commSemiring', which is 'nonco
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean:115:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'sigma', which is 'noncomputable'
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean:123:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.nonAssocSemiring', which is '
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean:141:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.ring', which is 'noncomputabl
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-char-zero-host-letters`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
