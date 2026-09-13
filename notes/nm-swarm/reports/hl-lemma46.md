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
  - `PocketCellTransportStatement`, a hypothesis of `fourSectionCuts_cellTransport`, is go-lemma42's.
- hW is one line from closed, in simple-group's `FinitelyPresentedInfiniteSimpleClosed`. It needs an import of `QTwoLemmaFourSixDynamics` and `finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics`. This was reported to the lead; the file is not this lane's.

## Census
- `metadata/nm-census-rows/hl-lemma46.tsv`: LINE:1679 `partial` (the FFF §2 "finitely presented infinite simple group", witness Q₂), carrying the dynamics.
- The W1 modules are infrastructure for `thm:hull` (tex 1636). They certify no printed sentence on their own, so they have no rows.

## Next
- The Corollary 7.4 piece was superseded: cite-hull closed Hull Cor 7.4 (c6e0b6c33).
- Done for W1: the CutMerge repair and the two-collar lemma. SHAs and statement were sent to hull-select and main.
- Held: no edits to `OsinAppendixCutMerge` until ghw-charp2 reports its patch 05 landed.
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
  - Drafts staged in the lane scratchpad, unprobed, for whichever sub-step kh-ejz names:
    - `$NM/drafts/hl-lemma46-OsinPocketWalkColouring.lean`, the pocket-level assembly:
      - `sideFaces_subset_of_colouring`: the side of the walk lies in every colour class that holds the walk darts. No connectivity is used.
      - `sideFaces_colouring`: conversely, on a planar map the side of a noncrossing walk is a colour class.
      - `isNoncrossingClosedWalk_of_colouring`, `PocketWalk.toPocketFaceSetOfColouring`, `PocketWalk.exists_pocketFaceSet_of_orient`. The last takes (iii'), (C) as `horient`, and (ii) as `hkept`.
    - `$NM/drafts/hl-lemma46-OsinPocketPinchedTwoGonColouring.lean`, the model tests:
      - On `lobeDiagram`, `pinchWalk : PocketWalk D 0 lobeDiagram 0 2` has walk `[5,3,4,6]`. `pinch_orient`: every colouring puts the four walk darts on one side, because the edges `{0,3}` and `{1,5}` lie on the walk. This is (C) on this map.
      - `PinchedWalkColouringModel`: a pocket face set with the walk as boundary cycle and the digon `a` kept.
      - `PinchedWalkNoKeptCell`: on `diagram`, no colour class holds both the walk darts and a relator cell. So (ii) does not follow from (iii') and (C).
      - `LakeWalkColouringModel`: the rose with walk `[0,2]`.
    - These overlap kh-ejz's planned (C) model tests. They land only if kh-ejz names them.
