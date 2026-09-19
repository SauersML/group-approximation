---
rg: 2
id: fix-bhmet-char-zero-coords-denominators
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators: Application type mismatch: The argument"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**RESOLVED (2d6ebaf55).** Lean module `GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean` failed to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** 90089df2a1: BH metabelian chain: generic clearing-denominators lemma; two latent Subgroup API fixes (u. It was OPEN until a trusted probe built it green; see below.

**Green.** Built green (lake ✔ or replay) by the trusted gqprobe-lean v4 batch, Slurm job 1328760 (request log gq-slurm/batch-b1789769423-3.log, lane bh-pal-wire). That build used base d2df12ed9 plus the overlay later landed as 2d6ebaf55, and no other overlay was in the batch. The job was cancelled after these modules had compiled. Since then no file in this module's import closure has changed on main, only downstream modules and a lakefile comment. That cancellation is why the index loop, which requires a completed batch, did not record it.

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
