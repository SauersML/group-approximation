# hl-lemma46 (lane report, 2026-09-13)

Scope: Hyde–Lodha Lemma 4.6 (tex 867–869, `\label{FPlem3}`), at the generality Proposition 4.7
consumes. The 09-13 final split (roster) runs through simple-group's interface
`HydeLodha/QTwoLemmaFourSixStatements` (232d6b12b):
- hl-lemma46: `LemmaFourSixDynamicsStatement`.
- simple-group: `lemmaFourSixCaseOne_of_dynamics` and the final closed endpoint.
- kh-ejz: the casing pair and conjugation into the unit frame.
- fff-quotient: |I| = 1.

## Landed
- `HydeLodha/QTwoLemmaFourSixDynamics` (de535e84c; probe 0913-021539-18816 PROBE GREEN, BUILT, bytes = origin/main; closed axioms propext, Classical.choice, Quot.sound; in wire-queue).
  - Endpoint: `theorem lemmaFourSixDynamics : LemmaFourSixDynamicsStatement`, with `#audit_closed_axioms`.
  - Helpers, with `#audit_axioms`:
    - `germRight_iterate_le`: mirror of `germLeft_iterate_ge`.
    - `disjoint_perIoo_of_le`: disjoint periodic intervals.
    - `exists_upsilon_gammaTwo_move`: `exists_move` made periodic through `perHom 4` and `upsilon_gammaTwo_eq_map`.
    - `exists_upsilon_qTwo_push`: one `t ∈ Υ_{Q₂}([e₁, e₂])` with `t d ≤ c`, the commutator of two moves.
    - `disjoint_pow_image`: the intervals `[c, d]·t^j` are pairwise disjoint.
- W1 for hull-select: the repair of `Estimating/OsinAppendixCutMerge` (e7e55c0f2; in wire-queue).
  - The file moved from hull-respell's `.files` to this lane.
  - Probe 0913-090304-65564 built it together with hull-select's `OsinPocketZeroCellMerge`: PROBE GREEN, both BUILT.
  - The red at line 103: in `false_of_cons_singleton`, `omega` treated `family.card` over `RegionCandidate D eps Xi` and over the unfolded sigma type that `Finset.card_cons` infers as two different atoms. An explicit type on `hconscard` fixes it. No statement changed.
- W1 for hull-select and dgo-analytic: `Estimating/OsinPocketTwoCollars`.
  - First landing 282e3a821 (probe 0913-091355-26476). The current version is 7eb17a3e9: probe 0913-092959-67901 PROBE GREEN, BUILT; axioms propext, Classical.choice, Quot.sound; in wire-queue.
  - Split confirmed with kh-torsion: this lane owns the double collar; kh-torsion proves `GeodesicCollarStatement`.
  - `PocketRegion.exists_twoCollars_of_ne_or`: the general form, suggested by kh-torsion for dgo-analytic's `PocketCollarStatement`, whose arcs may be empty.
    - It assumes `t₁ ≠ [] ∨ t₂ ≠ [] ∨ listVal (dartWord s₁) ≠ 1 ∨ listVal (dartWord s₂) ≠ 1`.
    - A side of value `≠ 1` makes its word, and so its side and its collar, nonempty. That discharges both collar steps.
  - `PocketRegion.exists_twoCollars`: sub-piece 2 of MultipleEdgeCut, with the statement hull-select specified. It is the case `t₁ ≠ []` of the general form; its unused `ht₂` is spelled `_ht₂`.
    - It takes a pocket with inverse complement cycle `s₁ t₁ s₂ t₂`, where `t₁` and `t₂` are nonempty.
    - It returns an O-equivalent diagram whose pocket reads `c₁ t₁ c₂ t₂`, with `c₁` reading `g₁` and `c₂` reading `g₂`.
    - Also returned: the dart embedding, the outer boundary, the outside cells, and each relator cell staying on its side.
    - Proof: kh-torsion's `GeodesicCollarStatement` along `s₁`, a `PocketRegion.withOuter` restart, the collar along the image of `s₂`, and a second restart.
    - The collar statement is a hypothesis of this lemma, as hull-select specified; kh-torsion owns it.
  - `Embedded.dartWord_map_embedding`: a label-preserving embedding of darts preserves words.

## Construction (tex 874, 877–878, 888–889)
- **f.** `exists_upsilon_qTwo_germs` gives `f ∈ Υ_{Q₂}(I)` with the germ `t ↦ a + 6 (t − a)` at `a⁺` and the germ `t ↦ b + 6 (t − b)` at `b⁻`.
- **The intervals.** `λ = 6^{-L} ≤ min(ε, (b − a)/20)`. Then `J = [e₁, e₂] = [a + λ, b − λ]` and `[c, d] = [a + 2λ, b − 2λ]`. The germs give `f e₁ = a + 6λ ≥ c` and `f e₂ = b − 6λ ≤ d`.
- **Covering.** Take `k ∈ Υ^c_{Γ₂}(I)`, supported in `(a + δ, b − δ)`.
  - Choose `N` with `6^N min(δ, λ) ≥ 1`. The germ iterates put `f^N(a + δ') ≥ a + λ` and `f^N(b − δ') ≤ b − λ`.
  - One more step of `f` gives `a + 6λ` and `b − 6λ`.
  - So `f^{N+1} k f^{-(N+1)} ∈ Υ^c_{Γ₂}([c, d])` with margin `λ`.
- **The s_i.** `s_i = t^{i+1}`.
  - `K ∈ Υ_{Γ₂}(J)` moves a grid point `β ∈ (d, e₂)` below a grid point `α ∈ (e₁, c)`.
  - `H ∈ Υ_{Γ₂}([α, β])` moves `d` below `c`.
  - `t = ⁅H, K⁆ ∈ Q₂` is supported in `J`, and `t d = H d ≤ c`, because `K⁻¹ d ∈ [β, e₂]` is fixed by `H`.
  - `t^j d` decreases and `t^{j+1} d ≤ t^j c`, so the images `[c, d]·t^j` are pairwise disjoint and disjoint from `[c, d]`.

## Residual
- None in this lane: `LemmaFourSixDynamicsStatement` is closed.
  - The two W1 pieces carry no residual Prop of this lane.
  - `GeodesicCollarStatement`, a hypothesis of `exists_twoCollars`, is kh-torsion's.
  - `PocketCellTransportStatement`, a hypothesis of `fourSectionCuts_cellTransport`, is closed by go-lemma42's `pocketCellTransport` (874a332a2, `Estimating/OsinPocketGlueCellTransport:164`).
    - hull-select's `OsinPocketMultipleEdgeAssembly:172` still passes it as `hcell`. Passing `pocketCellTransport` there is the consumer owner's edit.
- hW is one line from closed, in simple-group's `FinitelyPresentedInfiniteSimpleClosed`. It needs an import of `QTwoLemmaFourSixDynamics` and `finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics`. This was reported to the lead; the file is not this lane's.

## Census
- `metadata/nm-census-rows/hl-lemma46.tsv`: LINE:1679 `partial` (the FFF §2 "finitely presented infinite simple group", witness Q₂), carrying the dynamics.
- The W1 modules are infrastructure for `thm:hull` (tex 1636). They certify no printed sentence on their own, so they have no rows.

## Next
- The Corollary 7.4 piece was superseded: cite-hull closed Hull Cor 7.4 (c6e0b6c33).
- Done for W1: the CutMerge repair and the two-collar lemma. SHAs and statement were sent to hull-select and main.
- Hold lifted on `OsinAppendixCutMerge`: ghw-charp2's patch 05 landed at f04929ebb, and co-probe 0913-144505-9146 is GREEN with CutMerge built.
  - The patch passes `R.regionFamily_noLoop` as the new `hloop` argument of `respectsSections_of_sameTargetProfile` (l.147), and rewords the docstrings of `false_of_cons_singleton` and `false_of_collapse_singleton` ("from a cell to a different cell or to a section").
  - No statement changed. The loop conjunct sits inside `RespectsSections`, so at site 1 it is the caller's hypothesis. No edit of this lane is pending there.
- Current item (lead, 09-13 ~09:45): census the open W1 leaf Props, then prove the first unowned leaf.
  - Census sent to the lead: `$NM/drafts/w1-leaves-0913.md`, pinned at origin dc23e61b1.
  - Every leaf on the ruled `_of_pocketParts` route has a named owner.
  - The only leaves no lane owns are `EstimatingJointConstructionStatement` and `PrefixKernelConeCutInductionStatement`, on the dead `_of_reduced` route. Taking either would duplicate W1.
  - Stale owner: C6′ `TwoGonHoldsInput` (`Estimating/OsinAppendixEulerSmallFaces:94`). The roster names debt-conditional, but that lane has no module and no report entry for it.
  - Ruled (lead, 09-13): C6′ stays with debt-conditional, which is working on it. This lane does not start it. The census goes into the roster.
  - Risk on the docstring route of C6′: `PocketRegion.ofSimpleClosedWalk` needs the merged walk (source arc reversed, right side of `a`, target arc, left side of `b`) to be simple. dgo-geometric's `OsinPocketPinchedTwoGonRegion` (`not_isSimpleClosedWalk`) shows a pinched pocket, so the route needs a no-pinch lemma for the optimum or a producer for pinched pockets.
- Done for hull-select (team-lead: "hl-lemma46 joins as your helper"): `Estimating/OsinPocketMultipleEdgeTransport` at 1d177113c. Probe 0913-104724-79095: PROBE GREEN, BUILT, bytes = origin/main; axioms propext, Classical.choice, Quot.sound; in wire-queue. SHA and statement sent to hull-select.
  - `PocketRegion.fourSectionCuts_cellTransport`, with the statement hull-select specified: regions to sections `1` and `3` of the four-part multiple-edge pocket cut glue back into cell-to-cell regions. It is the `htransport` argument of `OsinMultipleEdgeCut.ofPocketRegion`.
  - Proof: `PocketCellTransportStatement` (go-lemma42) at `pre = s₁` and at `pre = s₁ t₁ s₂`, as in `hcellT` and `hsecT` of `PocketCarrier.nonempty_osinSectionPocketCut`. The four `partsCut` evaluations are re-proved locally, because the originals are private.
  - Residual: `PocketCellTransportStatement`, a binder standing for go-lemma42's Prop.
- Consumed: hull-select's `Estimating/OsinPocketMultipleEdgeAssembly` (2db85602c, `multipleEdgeCutInput_of_pieces`) uses `exists_twoCollars_of_ne_or` and `fourSectionCuts_cellTransport`. hull-select has no further sub-piece.
- Closed without a split: both pocket transports. `PocketOuterTransportStatement` is hull-select's `pocketOuterTransport` (71d59592c). `PocketCellTransportStatement` was proved in full by go-lemma42 (874a332a2).
- Current item (lead, 09-13 ~14:20): parity route (D). `U = {col = c0}` has `∂U = K.walk`, which feeds `toPocketFaceSetOfNoncrossing` (`OsinPocketSectionFaceSet:321`). cite-hull takes (C).
  - Asked kh-ejz for (B)'s signature and whether (D) is unstarted. If kh-ejz is already writing (D), this lane takes the sub-step kh-ejz names.
  - kh-ejz's `GGT/VanKampen/ClosedWalkFaceColouring` (probe 0913-142740-85270, PROBE GREEN) already holds (B) and the map-level (D):
    - (B): `exists_faceColouring` and `exists_faceSet_colouring`.
    - (D): `boundaryCycleOfColouring`. A face set that meets its complement exactly across the walk edges, and holds the faces of all walk darts, has the walk as a boundary cycle.
  - Nothing is built before kh-ejz's reply.
  - Candidate remainder, the pocket-level assembly: `PocketFaceSet.ofBoundaryCycle` on `boundaryCycleOfColouring` for `K.walk`.
    - (ii) `(cell X kept).face ∈ faces` is its only extra hypothesis.
    - `ClosedWalk` comes from chain and closes. Noncrossing comes from hull-respell's `BoundaryCycle.isNoncrossingClosedWalk` (`Estimating/OsinPocketClosedWalkNoncrossing:106`).
    - `toPocketFaceSetOfNoncrossing` would instead need `kept ∈ sideFaces`. Getting that from `kept ∈ U` needs `U ⊆ sideFaces`, which uses connectivity.
  - Hand model test of the map-level (D):
    - Pinched two-gon (`OsinPocketPinchedTwoGonModel`). `[5,3,4,6]` is a pocket walk: source cell 0 with arc `[0,1]` (invDarts `[5,3]`), and target arc `[4,6]` of outerDarts `[4,6,2]`.
      - The walk edges are `{5,1}`, `{3,0}`, `{4,8}`, `{6,9}`, and `{2,7}` is the only edge off the walk.
      - `U = pinchFaces` meets its complement exactly across the walk edges and holds the walk darts. So `∂U = {3,4,5,6}` (`isBoundaryDart_iff`), and the outer face 3 and the source face 0 lie outside.
      - (ii) fails: `U` holds no relator cell, so this model has no pocket face set.
    - Lake rose (`OsinPocketLakeModel`). Every edge is a walk edge, `U = {K}` and `∂U = {0,2}` is the walk; the lake and the outside lie outside.
  - kh-ejz's report (residual of `SectionPocketFaceSetInput`) lists (iii'), (C) and (ii), and names model tests of (C) on the pinched two-gon and on the lake complement `[3,1]` as its own next item. No reply from kh-ejz yet, so nothing of this item is built or landed.
  - Superseded, left unlanded: the draft assembly `$NM/drafts/hl-lemma46-OsinPocketWalkColouring.lean`. kh-ejz's `PocketWalk.exists_pocketFaceSet_closedWalk_of_orient` (ae463a301) and the model tests in `Estimating/OsinPocketColouringModel` (15504a498) cover it.
- Current item (lead, 09-13 15:50): piece (ii) of (D), the `hkept` binder of `exists_pocketFaceSet_closedWalk_of_orient`. kh-ejz owns binder 6 (`OsinSectionPocketFaceSetSectionStatement`) and consumes it. (C), cite-hull's `PocketWalkColourStatement`, is a named hypothesis until it lands.
  - Already on main: sec2-sentences' `pocketKeptCellNoncrossing` (`Estimating/OsinPocketKeptCellNoncrossing`, 3e7ce7227). It gives the kept cell from the family binders (`x ≠ y` selected, `hgap`, `hfirst`, `hsecond`, the output shape of (C)), `hvalue`, `hw` and `hfollows : (hw.outerCycle S.diagram.planar).FollowsBoundary`.
    - At binder 6, `hw` is `isNoncrossingClosedWalk_of_orient` from (C) and (iii'), and `hvalue` is `S.cell_listVal_ne_one hW hlambda hrho` (`Estimating/OsinLemma94PolygonCovers:80`) with `c < lambda * rho`.
  - The gap is `hfollows`, which fails at a lake.
    - dgo-analytic's `OsinPocketLakeLabelledModel` (494dc3249) puts a relator cell on the side of the rose walk `[0,2]`, while `lakeCycle_outerCycle_not_followsBoundary` holds for that walk.
    - The lake case of kh-ejz's `OsinPocketColouringModel` shows that (C) and (iii') do not exclude lakes.
    - hull-select's first-turn producer (`FirstTurnWalkPocketInputsStatement`, a29b02280) needs a first-turn chain on the complement spelling, and that chain fails at a lake (`lake_not_firstTurn`).
  - The absorption proof (`exists_kept_of_pocketRegion_of_value`, `subset_of_not_disjoint_pocketRegion`, `InnerDiscRegion.ofPocketRegion`) reads only `P.faces`, `P.inner` and `P.outerFace_not_mem`, never `P.outer`. So `hfollows` enters only through `heuler`. hull-euler's torus rose `[0,2,4]` (`NoncrossingClosedWalkEuler` docstring) shows that without it the inner Euler equation can fail for a noncrossing walk.
  - Routes to the inner disc on `sideFaces`:
    - If the outer cycle follows its boundary: `reclosed_euler`, the landed route.
    - If the inner cycle follows its boundary: `BoundaryCycle.toDiscRegion_of_followsBoundary` (`SurgeryReclosedPlanarity:36`). Both lake models have it (`lakeCycle_innerCycle_followsBoundary`, `pocketCycle_innerCycle_followsBoundary`).
    - If neither follows (a pinch and a lake together, or the torus rose): open.
  - Proposal sent to kh-ejz at 16:23, in one message; awaiting the reply. Nothing is built before agreement.
    - F1: `PocketWalkKeptCellStatement`, which is `PocketKeptCellNoncrossingStatement` with the `hfollows` binder deleted, in a new module `Estimating/OsinPocketWalkKeptCell`.
    - F2, the fallback: sec2-sentences' Prop as landed. kh-ejz passes `hfollows`, and lake exclusion becomes a named residual.
    - Also asked: `hvalue`, or `(hW : OsinCCondition …) (hlambda) (hrho)` in its place.
  - Model test plan for the agreed statement:
    - Positive: on `lobeDiagram`, `pinchWalk` with kept cell `⟨1,_⟩` (draft `$NM/drafts/hl-lemma46-OsinPocketPinchedTwoGonColouring.lean`).
    - Calibration: on `diagram`, `hw`, `hout`, `hfollows` and `heuler` hold for `[5,3,4,6]`, but no relator cell lies on the side, so the family binders carry the proof.
