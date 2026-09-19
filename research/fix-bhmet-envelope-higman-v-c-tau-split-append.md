---
rg: 2
id: fix-bhmet-envelope-higman-v-c-tau-split-append
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitAppend: `simp only` leaves two `if`s that differ only in their Decidable instances"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauSplitAppend.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 1 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**Repair landed, unprobed.** 2dd8b94c03: BH metabelian: static repairs for the 8 NEW-RED modules of probe b1789834028, with fix nod. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVCTauSplitAppend.lean:68:71: unsolved goals
```

**Kind.** mechanical: after the `head?` rewrite, the two sides carry different `Decidable (some e = some x)` instances, so the syntactic `rfl` that `simp` tries fails.


**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitAppend` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
