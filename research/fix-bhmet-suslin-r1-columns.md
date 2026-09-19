---
rg: 2
id: fix-bhmet-suslin-r1-columns
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinR1Columns: lambda binders elaborated at `ι` instead of `{k // k ≠ t}`"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 9 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**Repair landed, unprobed.** 2dd8b94c03: BH metabelian: static repairs for the 8 NEW-RED modules of probe b1789834028, with fix nod. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean:41:51: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
error: GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean:41:65: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean:43:39: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean:60:45: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
error: GroupApproximation/BooneHigman/Metabelian/SuslinR1Columns.lean:60:59: Application type mismatch: The argument
```

**Kind.** elaboration order: in `l.map fun k ↦ elementaryUnit (k : ι) …`, the ascription `(k : ι)` fixes the binder type to `ι` before the list's element type propagates. The whnf timeout at 67 and the unknown constant at 113 follow from it.


**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinR1Columns` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
