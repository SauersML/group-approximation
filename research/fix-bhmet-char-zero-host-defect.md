---
rg: 2
id: fix-bhmet-char-zero-host-defect
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Defect: noncomputable definitions, unresolved `Pi.single` codomain, and binop terms applied before their type is known"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 7 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean:29:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.ring', which is 'noncomputable'
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean:35:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.ring', which is 'noncomputable'
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean:51:60: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean:53:61: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Defect.lean:147:7: Function expected at
```

**Kind.** mechanical (noncomputable) plus elaboration order.

**Repair landed, unprobed.** fix-bh-b wraps the namespace body in `noncomputable section` … `end`. The right-hand `Pi.single` terms in natVec_single are ascribed `(Pi.single j 1 : Fin n → MvPolynomial (Fin k) A) j`. Both sides of `hW` in sigma_Zv get the ascription `(… : Fin n → MvPolynomial (Fin k) A)` before they are applied to `j`. The unsolved `case e_a` at 140 is the tail of sigma_Zv that did not run once `hW` failed.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Defect` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
