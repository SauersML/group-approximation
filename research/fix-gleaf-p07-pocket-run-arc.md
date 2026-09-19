---
rg: 2
id: fix-gleaf-p07-pocket-run-arc
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc: strict-implicit binder of `List.Subset`"
---

Recorded against the non-MF chain (GreendlingerLeaf P07InnerPocket). It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/PocketRunArc.lean` failed to build in direct batch b1789850259 (09-19, base 13d4765e1b, empty overlay; union log gq-slurm/batch-b1789850259-all.log). It blocks 11 of the modules touched by the `open scoped List` sweep 9ddeaca04a. Its imports built green, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**Repair landed, unprobed.** 4b1ff63c66: GreendlingerLeaf P07: fix WitnessStepBridgeMirror and PocketRunArc, which block 11 open-sc. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/PocketRunArc.lean:107:52: Application type mismatch: The argument
```

**Kind.** Lean core drift: `List.Subset` is `∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂` in v4.32.0 (Init/Data/List/Basic.lean:1079), so `fun hx => hsub _ hx` binds `hx` to the dart and not to the membership proof. The `sorryAx` at 116 follows from it.


**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
