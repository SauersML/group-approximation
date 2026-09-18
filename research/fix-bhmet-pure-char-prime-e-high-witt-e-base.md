---
rg: 2
id: fix-bhmet-pure-char-prime-e-high-witt-e-base
kind: route
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighWittEBase.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighWittEBase.lean:125:27: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
