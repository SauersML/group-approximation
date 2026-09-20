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







**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:306:58: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:307:47: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean:330:14: 'GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHasse_exists_units_of_polyFun' depends on axioms outside the classical allowlist: [
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-pure-char-prime-e-high-artin-hasse-alg`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
