---
rg: 2
id: fix-bhmet-char-p-coords-assembly
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly: Unknown constant Algebra.fg_adjoin_finset"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPCoordsAssembly.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 3 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsAssembly.lean:60:12: Unknown constant `Algebra.fg_adjoin_finset`
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsAssembly.lean:61:33: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/CharPCoordsAssembly.lean:61:9: Tactic `rcases` failed: `x✝ : ?m.175` is not an inductive datatype
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-char-p-coords-assembly`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
