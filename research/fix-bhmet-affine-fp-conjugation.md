---
rg: 2
id: fix-bhmet-affine-fp-conjugation
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.AffineFPConjugation: `Pi.single i r` application type mismatch"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**RESOLVED (55aba370a4).** Lean module `GroupApproximation/BooneHigman/Metabelian/AffineFPConjugation.lean` failed to build in the trusted gqprobe-lean v4 batch, Slurm job 1328760 (09-18, base d2df12ed9 plus bh-pal-wire's wave-1 overlay; request log gq-slurm/batch-b1789769423-3.log; 3 error lines, including the axiom-guard lines that follow them). Its imports built green in that batch, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire. Node written by fix-bh-b.

**Green.** Built green (lake Built, no errors, so every `#audit_axioms` guard passed) in request 1 of bh-pal-wire's direct batch probe b1789834028 (09-19, acn112; base a39af618f3, empty overlay; log gq-slurm/batch-b1789834028-1.log). That request completed and was red only in modules outside this one's import closure. The compiled bytes are main's 55aba370a4 bytes, since the file is unchanged on main since then. None of the 5 files in its GroupApproximation import closure has changed on main since a39af618f3 (checked by fix-bh-b, 09-19).

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AffineFPConjugation.lean:98:47: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/AffineFPConjugation.lean:100:47: Application type mismatch: The argument
```

**Kind.** elaboration: `Pi.single i r` has an unresolved codomain family `?m i` inside `change`.

**Repair landed, unprobed.** 55aba370a4 (bh-pal-wire) adds the ascription `(Pi.single i r : I → R)` at both `change` sites (98, 100). The `sorryAx` at 107 follows from those. fix-bh-b reviewed it statically (09-19) and found nothing further.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AffineFPConjugation` compile with the repository's `-DwarningAsError=true` settings, changing no statement. Slurm submission has been blocked since 09-18 ~20:55 (state/SLURM-BLOCKED), so no trusted build has run since the repair landed.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
