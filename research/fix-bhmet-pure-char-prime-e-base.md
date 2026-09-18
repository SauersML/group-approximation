---
rg: 2
id: fix-bhmet-pure-char-prime-e-base
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEBase: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEBase.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEBase.lean:53:27: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEBase.lean:51:29: unsolved goals
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEBase.lean:57:27: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEBase.lean:55:30: unsolved goals
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-pure-char-prime-e-base`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEBase` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
