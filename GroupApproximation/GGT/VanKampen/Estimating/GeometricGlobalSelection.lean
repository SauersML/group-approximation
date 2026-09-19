import GroupApproximation.GGT.VanKampen.Estimating.GeometricWeightBound
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

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

theorem OEquivalentDiscDiagram.sum_perimeter_eq
    {Xi : DiscDiagram.{u, w, v} W} (E : OEquivalentDiscDiagram Delta Xi) :
    (∑ i : Fin Xi.rCellCount, (cell Xi i).word.length) =
      ∑ i : Fin Delta.rCellCount, (cell Delta i).word.length := by
  rw [← Equiv.sum_comp E.cellIndex (fun i => (cell Xi i).word.length)]
  apply Finset.sum_congr rfl
  intro i _
  rw [E.cellWord_eq i]

/-- One actual compatible family on a reduced O-equivalent diagram. -/
structure RealizedGeometricFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta diagram
  reduced : diagram.Reduced
  family : Finset (GeometricCandidate D eps diagram)
  pairwise : EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family

namespace RealizedGeometricFamily

def weight (S : RealizedGeometricFamily D eps Delta) : ℕ :=
  EstimatingSelection.familyWeight GeometricCandidate.weight S.family

theorem weight_le (S : RealizedGeometricFamily D eps Delta) :
    S.weight ≤ (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) +
      Delta.boundaryWord.length := by
  have h := GeometricCandidate.familyWeight_le S.family S.pairwise
  rwa [S.equiv.sum_perimeter_eq, S.equiv.boundaryWord_eq] at h

def empty (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) (hred : Delta.Reduced) :
    RealizedGeometricFamily D eps Delta where
  diagram := Delta
  equiv := OEquivalentDiscDiagram.refl Delta
  reduced := hred
  family := ∅
  pairwise := by intro a ha; simp at ha

end RealizedGeometricFamily

/-- Maximal actual arc weight, then minimum number of regions, across all
reduced O-equivalent diagrams, with both comparisons on retained witnesses. -/
structure GloballyDistinguishedGeometricFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) extends RealizedGeometricFamily D eps Delta where
  weight_maximal : ∀ other : RealizedGeometricFamily D eps Delta,
    other.weight ≤ toRealizedGeometricFamily.weight
  card_minimal : ∀ other : RealizedGeometricFamily D eps Delta,
    other.weight = toRealizedGeometricFamily.weight → family.card ≤ other.family.card

/-- The perimeter bound gives an attained maximum; well-ordering then
supplies an attained minimum cardinality at that maximum. -/
theorem exists_globallyDistinguishedGeometricFamily
    (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (hred : Delta.Reduced) : Nonempty (GloballyDistinguishedGeometricFamily D eps Delta) := by
  let bound := (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) + Delta.boundaryWord.length
  let values := (Finset.range (bound + 1)).filter fun n =>
    ∃ S : RealizedGeometricFamily D eps Delta, S.weight = n
  have hmem (S : RealizedGeometricFamily D eps Delta) : S.weight ∈ values := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, S, rfl⟩
    have h := S.weight_le
    change S.weight ≤ bound at h
    omega
  have hnonempty : values.Nonempty :=
    ⟨(RealizedGeometricFamily.empty D eps Delta hred).weight,
      hmem (RealizedGeometricFamily.empty D eps Delta hred)⟩
  obtain ⟨maximum, hmaximum, hmaximal⟩ := Finset.exists_max_image values id hnonempty
  obtain ⟨initial, hinitial⟩ := (Finset.mem_filter.mp hmaximum).2
  have hexists : ∃ k : ℕ, ∃ S : RealizedGeometricFamily D eps Delta,
      S.weight = maximum ∧ S.family.card = k :=
    ⟨initial.family.card, initial, hinitial, rfl⟩
  obtain ⟨S, hweight, hcard⟩ := Nat.find_spec hexists
  refine ⟨{ toRealizedGeometricFamily := S, weight_maximal := ?_, card_minimal := ?_ }⟩
  · intro other
    rw [hweight]
    exact hmaximal other.weight (hmem other)
  · intro other heq
    rw [hcard]
    apply Nat.find_min' hexists
    exact ⟨other, heq.trans hweight, rfl⟩

/-- Restricting the attained global optimum to its own diagram gives the
ordinary finite Definition-M family on actual geometric candidates. -/
def GloballyDistinguishedGeometricFamily.toDistinguishedFamily
    (S : GloballyDistinguishedGeometricFamily D eps Delta) :
    EstimatingSelection.DistinguishedFamily
      (GeometricCandidate.Compatible (D := D) (eps := eps) (Delta := S.diagram))
      GeometricCandidate.weight where
  family := S.family
  pairwise := S.pairwise
  weight_maximal := fun other hother =>
    S.weight_maximal { S.toRealizedGeometricFamily with family := other, pairwise := hother }
  card_minimal := fun other hother heq =>
    S.card_minimal { S.toRealizedGeometricFamily with family := other, pairwise := hother } heq

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OEquivalentDiscDiagram.sum_perimeter_eq
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedGeometricFamily.weight_le
#audit_axioms GroupApproximation.GGT.VanKampen.exists_globallyDistinguishedGeometricFamily
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedGeometricFamily.toDistinguishedFamily
