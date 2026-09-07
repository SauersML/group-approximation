import GroupApproximation.GGT.VanKampen.Estimating.RegionWeightBound
import GroupApproximation.GGT.VanKampen.Estimating.GeometricGlobalSelection

/-!
# Selecting actual contiguities over O-equivalent diagrams

The total selected weight is bounded by the original relator and exterior
perimeters, even when G-cell subdivisions vary. A maximum is therefore
attained among all reduced O-equivalent diagrams in the same dart universe.
Among all such maximizers we choose minimum family cardinality. This is an
actual existence proof; neither optimum is an input to the construction.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open Embedded
open scoped Classical

/-- One actual compatible family on a reduced O-equivalent diagram. -/
structure RealizedRegionFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta diagram
  reduced : diagram.Reduced
  family : Finset (RegionCandidate D eps diagram)
  pairwise : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family

namespace RealizedRegionFamily

def weight (S : RealizedRegionFamily D eps Delta) : ℕ :=
  EstimatingSelection.familyWeight RegionCandidate.weight S.family

theorem weight_le (S : RealizedRegionFamily D eps Delta) :
    S.weight ≤ (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) +
      Delta.boundaryWord.length := by
  have h := RegionCandidate.familyWeight_le S.family S.pairwise
  rwa [S.equiv.sum_perimeter_eq, S.equiv.boundaryWord_eq] at h

def empty (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) (hred : Delta.Reduced) :
    RealizedRegionFamily D eps Delta where
  diagram := Delta
  equiv := OEquivalentDiscDiagram.refl Delta
  reduced := hred
  family := ∅
  pairwise := by intro a ha; simp at ha

end RealizedRegionFamily

/-- Maximal actual arc weight, then minimum number of regions, across all
reduced O-equivalent diagrams, with both comparisons on retained witnesses. -/
structure GloballyDistinguishedRegionFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) extends RealizedRegionFamily D eps Delta where
  weight_maximal : ∀ other : RealizedRegionFamily D eps Delta,
    other.weight ≤ toRealizedRegionFamily.weight
  card_minimal : ∀ other : RealizedRegionFamily D eps Delta,
    other.weight = toRealizedRegionFamily.weight → family.card ≤ other.family.card

/-- The perimeter bound gives an attained maximum; well-ordering then
supplies an attained minimum cardinality at that maximum. -/
theorem exists_globallyDistinguishedRegionFamily
    (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (hred : Delta.Reduced) : Nonempty (GloballyDistinguishedRegionFamily D eps Delta) := by
  let bound := (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) + Delta.boundaryWord.length
  let values := (Finset.range (bound + 1)).filter fun n =>
    ∃ S : RealizedRegionFamily D eps Delta, S.weight = n
  have hmem (S : RealizedRegionFamily D eps Delta) : S.weight ∈ values := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, S, rfl⟩
    have h := S.weight_le
    change S.weight ≤ bound at h
    omega
  have hnonempty : values.Nonempty :=
    ⟨(RealizedRegionFamily.empty D eps Delta hred).weight,
      hmem (RealizedRegionFamily.empty D eps Delta hred)⟩
  obtain ⟨maximum, hmaximum, hmaximal⟩ := Finset.exists_max_image values id hnonempty
  obtain ⟨initial, hinitial⟩ := (Finset.mem_filter.mp hmaximum).2
  have hexists : ∃ k : ℕ, ∃ S : RealizedRegionFamily D eps Delta,
      S.weight = maximum ∧ S.family.card = k :=
    ⟨initial.family.card, initial, hinitial, rfl⟩
  obtain ⟨S, hweight, hcard⟩ := Nat.find_spec hexists
  refine ⟨{ toRealizedRegionFamily := S, weight_maximal := ?_, card_minimal := ?_ }⟩
  · intro other
    rw [hweight]
    exact hmaximal other.weight (hmem other)
  · intro other heq
    rw [hcard]
    apply Nat.find_min' hexists
    exact ⟨other, heq.trans hweight, rfl⟩

/-- Restricting the attained global optimum to its own diagram gives the
ordinary finite Definition-M family on actual geometric candidates. -/
def GloballyDistinguishedRegionFamily.toDistinguishedFamily
    (S : GloballyDistinguishedRegionFamily D eps Delta) :
    EstimatingSelection.DistinguishedFamily
      (RegionCandidate.Compatible (D := D) (eps := eps) (Delta := S.diagram))
      RegionCandidate.weight where
  family := S.family
  pairwise := S.pairwise
  weight_maximal := fun other hother =>
    S.weight_maximal { S.toRealizedRegionFamily with family := other, pairwise := hother }
  card_minimal := fun other hother heq =>
    S.card_minimal { S.toRealizedRegionFamily with family := other, pairwise := hother } heq

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RealizedRegionFamily.weight_le
#audit_axioms GroupApproximation.GGT.VanKampen.exists_globallyDistinguishedRegionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedRegionFamily.toDistinguishedFamily
