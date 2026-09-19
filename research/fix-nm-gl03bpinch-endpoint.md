---
id: fix-nm-gl03bpinch-endpoint
kind: claim
rg: 2
title: "Probe GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint: its recorded build blocker is gone; statically consistent, never built"
---

Recorded against `thm:hull` through the Greendlinger waist. `Full/GL06/Assembly` (`relativeGreendlinger_zero_of_allCells_of_core`, the minimal two-residual route to `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`) imports this module, so hG cannot build until it does.

**UNPROBED.** No edit is needed. The build caveat in `Piece07Below/RerouteEndpoint.lean` and `P07InnerPocket/PinchAbsPinchCorrBridge.lean` is stale. Both say `GL03BPinchOrder.Order` and `GL03BPinchOrder.lakeWalk_reverse_map_alpha_sublist` are missing, and both have been on main since 1fb0f3ac21 ("wire Endpoint import", 2026-09-18 17:00). No trusted build since then has reached this module: trusted build 3c8b417428 predates it, and batch 1338076 timed out.

**Static check against origin/main 6a01595a17 (lane nm-osin94, 2026-09-19; read, not built).**
- **Every name exists**: `GL03BPinchOrder.exists_lakeWalk_bothExterior_of_sublist` and `walk_eq_append_alpha_secondArcDart` (Split), `lakeWalk_reverse_map_alpha_sublist` (Order), the four `GL03BPinch.twoArcConclusion_of_*` (Cases), `TwoArcConclusion` (Cases), `InnerPocketEnclosedTwoArcCorrected`, `InnerPocketEnclosedTwoArcPinchedCorrected` and `innerPocketEnclosedTwoArcPinchedCorrected_of_corrected` (Statement).
- **The intro list matches the Statement's binders** one for one, 30 names from `G` to `hCb`.
- **The Order lemma's arguments line up.** `hinner` of the Statement is the lemma's Euler hypothesis with `hM := X.planar`. The `x₀` hole resolves to `secondArcDart K` from `walk_eq_append_alpha_secondArcDart`. Its conclusion `(lakeWalk …).reverse.map alpha <+ K.walk` is `invDarts X (lakeWalk …) <+ K.walk` by unfolding `invDarts` (`FaceSetWordHomotopyCore`: `darts.reverse.map Delta.toCombMap.alpha`).
- **Case calls match the Cases signatures**: `(K hw hoff hi hj hC hCf)`, and for the ordered case `(K hw hoff hi hj hx₀ heq hs₁ hs₂ hC hCf)`.
- **Universes**: `lakeWalk` takes `CombMap.{v}`, and the Order lemmas are universe-polymorphic.

**Remaining risk** (only a build can settle it): elaboration details such as the unification order for the `x₀` hole and `invDarts` resolution under the opened `Embedded` namespace, and whether `Split`, `Cases` and `Order` themselves build (none has a trusted green).

**Action.** First probe once Slurm returns: `gqprobe-lean.sh <lane> GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly` (empty overlay). If green, update the two stale caveats and the index line on FIX-GRAPH. Owner: nm-osin94 (static), nm-gl06e (consumer).
