---
id: fix-nm-uncond-b-closed-walk-excise-wrap
kind: claim
rg: 2
title: "Fix GroupApproximation.GGT.VanKampen.ClosedWalkExciseWrap: unprobed pinch-excision lemmas (end and wrapping cases)"
---

**Module.** `GroupApproximation/GGT/VanKampen/ClosedWalkExciseWrap.lean`, a new unwired orphan from lane ms-nm-uncond-b. It is **unprobed**: Slurm submission is blocked for the group (SLURM-BLOCKED), so no build has run and no error is known. There are no hypotheses standing in for claims. Every theorem is a plain list-and-walk lemma.

**Content.** It does sub-step 3 of the quadrant move on nm-gl03d's board (`GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement`, the other session's lane gl-p10-91). All four lemmas build on nm-osin94's `IsClosedDartWalk.excise_take_drop` (`ClosedWalkExcise`, 898282cd50). Each takes the pinch in the form "after `walk[j-1]` the walk is back at the vertex of `walk[i]`":
* `excise_take_drop_alpha`: `walk.take i ++ walk.drop j` is closed, for `i < j ≤ walk.length`, including `j = walk.length`, when that list is nonempty;
* `middle_of_pinch`: the removed stretch `(walk.drop i).take (j - i)` is itself closed (the wrapping case);
* `middle_of_wrapPinch`: the same, with the pinch stated on the wrapping removed stretch;
* `vertexOf_alpha_getElem_pred`: the chain step, `walk[k-1]` ends where `walk[k]` begins.

**What it needs.** One trusted build of this module (it imports only `ClosedWalkExcise` and `Meta.AxiomGuard`), queued for when Slurm is unblocked.

**Resolve when.** The module is green on main. Then flip this node to RESOLVED and cite the green commit.
