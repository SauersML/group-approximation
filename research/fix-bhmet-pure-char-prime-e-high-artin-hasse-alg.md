---
rg: 2
id: fix-bhmet-pure-char-prime-e-high-artin-hasse-alg
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg: automatically included section variable(s) unused in theorem ..."
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 8 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.


**Still red after wave 1** (batch job 1328760, base d2df12ed9). A second repair landed at 55aba370a, unprobed: MSI Slurm submission is blocked. It stays OPEN until a trusted probe builds it green.

**Repair landed, unprobed.** 55aba370a4: BH metabelian chain: second repair wave, unprobed (Slurm blocked). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:113:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHas
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:142:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHas
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:217:4: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:219:4: Application type mismatch: The argument
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-pure-char-prime-e-high-artin-hasse-alg`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
