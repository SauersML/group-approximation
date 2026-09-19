---
id: fix-nm-uncond-b-p10-rose-passages
kind: claim
rg: 2
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages: unprobed proof that the rose premises force a vertex with three passages"
---

**Modules.** Three new unwired orphans from lane ms-nm-uncond-b:
- `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10RosePassages/Basic.lean`: first edge darts under rotation, and the closure lemma;
- `.../P10RosePassages/Passages.lean`: (a) the alternation at a vertex, plus the two-passage identification of outs and ins;
- `.../P10RosePassages/Rose.lean`: (b) and (c).

They are **unprobed**. Slurm submission is blocked for the group (SLURM-BLOCKED), so no build has run and no error is known. They were written against origin/main 6a3f0c6cc5 without a build, so expect static errors when the first probe runs. There are no hypotheses standing in for claims.

**Content.** This is a sub-step of the quadrant move `GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement`, from the other session's lane gl-p10-91. Lane nm-gl03d named the sub-step and gave the paper proof (its board, "New lemma").
* `p10RP_not_turnCrossed` (b): at a vertex where at most two darts of the boundary cycle end, a non-first turn is not crossed.
* `p10RP_firstTurns_of_atMostTwo` (c): at most two passages everywhere, together with `p10FM_AllCrossed`, gives `p10FM_FirstTurns`.
* `p10RP_not_atMostTwo`: under the premises of the quadrant move, some vertex carries at least three passages.

The proof uses `BoundaryCycle.turn_mem_cycle`, `FirstTurn.reverse_map_alpha_iff` and `OuterPinchIsolated.{rel_next_of_isChain, isChain_of_rel_next}` from main.

**What it needs.** One trusted build of `P10RosePassages.Rose`, which imports the other two, once Slurm is unblocked. Then fix any static errors.

**Resolve when.** All three modules are green on main. Then flip this node to RESOLVED and cite the green commit.
