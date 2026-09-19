---
rg: 2
id: fix-gleaf-p07-witness-step-bridge-mirror
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeMirror: `rw [Equiv.Perm.inv_eq_iff_eq]` fails on the mirror's Dart type"
---

Recorded against the non-MF chain (GreendlingerLeaf P07InnerPocket). It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessStepBridgeMirror.lean` failed to build in direct batch b1789850259 (09-19, base 13d4765e1b, empty overlay; union log gq-slurm/batch-b1789850259-all.log). It blocks 11 of the modules touched by the `open scoped List` sweep 9ddeaca04a. Its imports built green, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessStepBridgeMirror.lean:88:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessStepBridgeMirror.lean:92:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_permCongr' dep
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessStepBridgeMirror.lean:102:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_mirror_faceCount' de
```

**Kind.** elaboration: the mirror's `Dart` equals `M.Dart` only after unfolding definitions, so `rw`'s keyed matching at `instances` transparency finds no occurrence of the pattern. The `sorryAx` lines at 92, 102, 111 and 118 follow from it.

**Repair landed, unprobed.** fix-bh-b replaces the rewrite with `refine Equiv.Perm.inv_eq_iff_eq.mpr ?_`, which unifies at default transparency. The rest of the proof is unchanged.

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeMirror` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
