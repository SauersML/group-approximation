---
rg: 2
id: fix-bhmet-pure-char-prime-e-high-witt-e-base
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase: failed to synthesize instance of type class"
---

**RESOLVED (2d6ebaf55).** Lean module `GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighWittEBase.lean` failed to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. It was OPEN until a trusted probe built it green; see below.

**Green.** Built green (lake ✔ or replay) by the trusted gqprobe-lean v4 batch, Slurm job 1328760 (request log gq-slurm/batch-b1789769423-3.log, lane bh-pal-wire). That build used base d2df12ed9 plus the overlay later landed as 2d6ebaf55, and no other overlay was in the batch. The job was cancelled after these modules had compiled. Since then no file in this module's import closure has changed on main, only downstream modules and a lakefile comment. That cancellation is why the index loop, which requires a completed batch, did not record it.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighWittEBase.lean:125:27: failed to synthesize instance of type class
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-pure-char-prime-e-high-witt-e-base`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
