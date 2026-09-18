import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Exclusion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremal.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCoreClose
import GroupApproximation.Meta.AxiomGuard

/-!
# `RoseExtremalJunctionStatement` is false

Lane gl-p10-51.

LOUD: this file closes in Lean the refutation of lane gl-p10-48 (there a Python model only).
`P10RoseExtremalTrim.RoseExtremalJunctionStatement` is FALSE, and with it
* `P10RoseExtremal.RoseExtremalRegionStatement`,
* `P10Rose.RoseSingleRegionMoveStatement`,
* `P10RegionMove.RoseExtremalCoreStatement`,
* `P10RegionMove.RegionMoveCoreCloseStatement`.

The counterexample is the gl-p10-40 G-face model with the label-1 edges subdivided once:
24 darts, two relator cells `S`, `K₀`, and the pocket face set `roseJunctionRefute_pK` at
`ε = 1` between the positions `0` and `5` of the exterior boundary.

Proof route:
* `roseJunctionRefute_not_junction`: the pocket meets every hypothesis
  (`P10RoseJunctionRefute/Premises`, `Area`); the three junctions make the listing a walk
  (`P10RoseExtremalTrim.isChain_listing_of_junctions`); no witness exists
  (`roseJunctionRefute_noWitness`).
* the corollaries: the existing reductions
  `P10RoseExtremalTrim.junction_of_extremalRegion`,
  `P10RegionMove.extremalJunction_of_extremalCore`,
  `P10RegionMove.regionMoveCoreClose_extremalCore_of_close`, and
  `roseJunctionRefute_regOfSingle` (a closed dart walk is a nonempty walk).

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

open OsinPocketPinchedTwoGonModel (D)

/-- **The extremal-region witness from a single-region move**: a closed dart walk is a nonempty
walk. -/
theorem roseJunctionRefute_regOfSingle (h : P10Rose.RoseSingleRegionMoveStatement.{u, w, v}) :
    P10RoseExtremal.RoseExtremalRegionStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, ⟨hne, hchain, _⟩,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hrout, hry, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, hne, hchain,
    hs₁, hs₂, hlo, hhi, ht₁, ht₂⟩

/-- **`RoseExtremalJunctionStatement` is false**, on the 24-dart pocket `roseJunctionRefute_pK`. -/
theorem roseJunctionRefute_not_junction :
    ¬P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0} := by
  intro h
  obtain ⟨r, hrout, _, source, kept, hsource, hkept, t₁, t₂, s₁, s₂, hperm, _, hs₁c, hs₂c, hj₁,
    hj₂, hj₃, hs₁, hs₂, _, hhi, ht₁, _⟩ := h D 1 roseJunctionRefute_X 0 5
      roseJunctionRefute_leastArea roseJunctionRefute_letters roseJunctionRefute_pK
      roseJunctionRefute_closedWalk roseJunctionRefute_notFirst roseJunctionRefute_srcLt
      roseJunctionRefute_tgtLt roseJunctionRefute_notUnpinched roseJunctionRefute_allCrossed
  exact roseJunctionRefute_noWitness r hrout source kept hsource hkept t₁ t₂ s₁ s₂ hperm
    (P10RoseExtremalTrim.isChain_listing_of_junctions t₁ t₂ hs₁c hs₂c hj₁ hj₂ hj₃) hj₂ hj₃
    hs₁ hs₂ hhi ht₁

/-- **`RoseExtremalRegionStatement` is false.** -/
theorem roseJunctionRefute_not_extRegion :
    ¬P10RoseExtremal.RoseExtremalRegionStatement.{0, 0, 0} := fun h =>
  roseJunctionRefute_not_junction (P10RoseExtremalTrim.junction_of_extremalRegion h)

/-- **`RoseSingleRegionMoveStatement` is false.** -/
theorem roseJunctionRefute_not_single : ¬P10Rose.RoseSingleRegionMoveStatement.{0, 0, 0} :=
  fun h => roseJunctionRefute_not_extRegion (roseJunctionRefute_regOfSingle h)

/-- **`RoseExtremalCoreStatement` is false.** -/
theorem roseJunctionRefute_not_extCore : ¬P10RegionMove.RoseExtremalCoreStatement.{0, 0, 0} :=
  fun h => roseJunctionRefute_not_junction (P10RegionMove.extremalJunction_of_extremalCore h)

/-- **`RegionMoveCoreCloseStatement` is false.** -/
theorem roseJunctionRefute_not_coreClose :
    ¬P10RegionMove.RegionMoveCoreCloseStatement.{0, 0, 0} := fun h =>
  roseJunctionRefute_not_extCore (P10RegionMove.regionMoveCoreClose_extremalCore_of_close h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_regOfSingle
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_not_junction
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_not_extRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_not_single
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_not_extCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_not_coreClose
