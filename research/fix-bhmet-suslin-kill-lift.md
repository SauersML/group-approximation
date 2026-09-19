---
rg: 2
id: fix-bhmet-suslin-kill-lift
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinKillLift: no `IsPrincipalIdealRing ℤ` instance in scope"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**RESOLVED (296aff5838, trusted batched probe job direct-b1789837230).** Previously OPEN. Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinKillLift.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 2 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinKillLift.lean:143:6: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/SuslinKillLift.lean:140:90: unsolved goals
```

**Kind.** missing import. `Submodule.IsPrincipal (Ideal.under ℤ J)` needs `IsPrincipalIdealRing ℤ`, which comes from `EuclideanDomain.to_principal_ideal_domain` and `Int.euclideanDomain` in `Mathlib.Algebra.EuclideanDomain.Int`. That module is not in this file's Mathlib import closure: fix-bh-b computed the 1570-module closure at pin 81a5d257 (09-19). So this is not the `Localization.Away` semiring diamond.


**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinKillLift` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
