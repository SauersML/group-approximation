import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.RegionCharge
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: the count, from the touch two-gons

`OsinLemma94ContactMapEmptyTwoGonInput` (`Estimating/OsinLemma94ContactMapHolds`) bounds the
nondegenerate small faces of `contactMap P` holding no object by `K n`.

* A face holding no object whose class reaches a selected region is charged to that region, and a
  region is charged at most once (`card_regionHeld_le`, `RegionCharge`): at most
  `#S.family ≤ 3 (n + r - 1) ≤ 12 n` such faces.
* The remaining faces are the **touch two-gons** `EmptyTouchTwoGonStatement`: nondegenerate small
  faces whose class reaches only darts based at the vertices of the face and at unselected
  `G`-faces, and no selected region.

`proof_of_touch` assembles the count with constant `K + 12` from a bound on the touch two-gons.

## The gap (not closed here)

This module provides no `theorem proof : OsinLemma94ContactMapEmptyTwoGonInput`;
`EmptyTouchTwoGonStatement` is reduced further in `P01EmptyTwoGon.TouchTwoGon`
(`touchTwoGon_of_corner`, `proof_of_corner`) to `TouchCornerStatement`: for maximal `P`, no touch
face exists (`CornerExcluded`).  An earlier pocket model (two cells touching at `m` points with rich
pocket faces) is excluded by `false_of_twoCellSides`, so it is not a counterexample.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

/-- **The touch two-gons** (open residual): under the binders of
`OsinLemma94ContactMapEmptyTwoGonInput`, the nondegenerate small faces holding no object and held
by no selected region number at most `K n`. -/
def EmptyTouchTwoGonStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    (Finset.univ.filter fun F : P.contactMap.Face =>
                      P.NondegenerateSmallFace F ∧ ¬ P.HoldsObject F ∧
                        ¬ ∃ a ∈ S.family, RegionHeld P F a).card ≤ K * Delta.rCellCount

/-- The empty small faces split into the region-held ones and the touch two-gons. -/
theorem empty_subset_union {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) :
    (Finset.univ.filter fun F : P.contactMap.Face =>
      P.NondegenerateSmallFace F ∧ ¬ P.HoldsObject F) ⊆
    (Finset.univ.filter fun F : P.contactMap.Face =>
      ¬ P.HoldsObject F ∧ ∃ a ∈ S.family, RegionHeld P F a) ∪
    (Finset.univ.filter fun F : P.contactMap.Face =>
      P.NondegenerateSmallFace F ∧ ¬ P.HoldsObject F ∧ ¬ ∃ a ∈ S.family, RegionHeld P F a) := by
  intro F hF
  obtain ⟨hnd, hnh⟩ := (Finset.mem_filter.mp hF).2
  by_cases hr : ∃ a ∈ S.family, RegionHeld P F a
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnh, hr⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd, hnh, hr⟩)

/-- **The empty two-gon count from the touch two-gons**, with constant `K + 12`: the region-held
faces number at most `#S.family ≤ 3 (n + r - 1) ≤ 12 n`.  This is a reduction; the touch residual is
open. -/
theorem proof_of_touch (htouch : EmptyTouchTwoGonStatement.{u, w, v}) :
    OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v} := by
  intro _ _ _ D hhyper lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e0, he0⟩ := htouch D hhyper lambda c mu h1 h2 h3 h4 h5
  refine ⟨e0, fun eps heps => ?_⟩
  obtain ⟨K, r0, hr0, hK⟩ := he0 eps heps
  refine ⟨K + 12, r0, hr0,
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax => ?_⟩
  have htb := hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax
  have hreg := card_regionHeld_le P hleast
  have hunion := (Finset.card_le_card (empty_subset_union P)).trans (Finset.card_union_le _ _)
  have hr := cuts.count_le
  have hmul : (K + 12) * Delta.rCellCount = K * Delta.rCellCount + 12 * Delta.rCellCount := by
    ring
  omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.proof_of_touch
