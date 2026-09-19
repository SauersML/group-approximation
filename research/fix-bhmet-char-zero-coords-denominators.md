---
rg: 2
id: fix-bhmet-char-zero-coords-denominators
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** 90089df2a1: BH metabelian chain: generic clearing-denominators lemma; two latent Subgroup API fixes (u. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean:84:43: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean:90:2: Unknown constant `GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mvPolynomial_mem_range_of_den_dvd`
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean:134:6: Unknown identifier `mvPolynomial_mem_range_of_den_dvd`
error: GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean:114:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-char-zero-coords-denominators`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
