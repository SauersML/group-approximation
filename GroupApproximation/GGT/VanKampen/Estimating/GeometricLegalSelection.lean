import GroupApproximation.GGT.VanKampen.Estimating.GeometricGlobalSelection
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet

/-!
# An attained optimum among diagrams with legal labels

The geometric candidates and their metric bounds continue to use D. A
separate alphabet E controls the labels allowed on the auxiliary diagram.
The normalized empty family supplies an actual eligible seed when E is the
symmetrized label alphabet of D, with no symmetry assumption on D.base.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D E : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

def RealizedGeometricFamily.LabelLegal (E : RelGenSet G Lambda)
    (S : RealizedGeometricFamily D eps Delta) : Prop :=
  ∀ d, E.IsLetter (S.diagram.label d)

structure LegallyDistinguishedGeometricFamily (D E : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) extends RealizedGeometricFamily D eps Delta where
  label_admissible : toRealizedGeometricFamily.LabelLegal E
  weight_maximal : ∀ other : RealizedGeometricFamily D eps Delta,
    other.LabelLegal E → other.weight ≤ toRealizedGeometricFamily.weight
  card_minimal : ∀ other : RealizedGeometricFamily D eps Delta,
    other.LabelLegal E → other.weight = toRealizedGeometricFamily.weight →
      family.card ≤ other.family.card

/-- Finite weight bounds and well-ordering apply inside the eligible class. -/
theorem exists_legallyDistinguished_of_seed
    (initial : RealizedGeometricFamily D eps Delta) (hlegal : initial.LabelLegal E) :
    Nonempty (LegallyDistinguishedGeometricFamily D E eps Delta) := by
  let bound := (∑ i : Fin Delta.rCellCount, (cell Delta i).word.length) + Delta.boundaryWord.length
  let values := (Finset.range (bound + 1)).filter fun n =>
    ∃ S : RealizedGeometricFamily D eps Delta, S.LabelLegal E ∧ S.weight = n
  have hmem (S : RealizedGeometricFamily D eps Delta) (hS : S.LabelLegal E) :
      S.weight ∈ values := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, S, hS, rfl⟩
    have h := S.weight_le
    change S.weight ≤ bound at h
    omega
  have hnonempty : values.Nonempty := ⟨initial.weight, hmem initial hlegal⟩
  obtain ⟨maximum, hmaximum, hmaximal⟩ := Finset.exists_max_image values id hnonempty
  obtain ⟨first, hfirstLegal, hfirst⟩ := (Finset.mem_filter.mp hmaximum).2
  have hexists : ∃ k : ℕ, ∃ S : RealizedGeometricFamily D eps Delta,
      S.LabelLegal E ∧ S.weight = maximum ∧ S.family.card = k :=
    ⟨first.family.card, first, hfirstLegal, hfirst, rfl⟩
  obtain ⟨S, hS, hweight, hcard⟩ := Nat.find_spec hexists
  refine ⟨{
    toRealizedGeometricFamily := S
    label_admissible := hS
    weight_maximal := ?_
    card_minimal := ?_ }⟩
  · intro other hother
    rw [hweight]
    exact hmaximal other.weight (hmem other hother)
  · intro other hother heq
    rw [hcard]
    apply Nat.find_min' hexists
    exact ⟨other, hother, heq.trans hweight, rfl⟩

/-- An actual normalized disc, with its empty compatible family, establishes
that the eligible optimization class is inhabited. -/
theorem exists_legallyDistinguishedGeometricFamily
    (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (hred : Delta.Reduced) (hboundary : RelWord.IsAdmissible D Delta.boundaryWord)
    (hcells : ∀ C ∈ Delta.relatorCells, RelWord.IsAdmissible D C.word) :
    Nonempty (LegallyDistinguishedGeometricFamily D (symmetricLabelAlphabet D) eps Delta) := by
  obtain ⟨R⟩ := symmetricLabelAlphabet.exists_normalization D Delta hboundary hcells
  let S : RealizedGeometricFamily D eps Delta := {
    diagram := R.diagram
    equiv := R.oEquivalent _
    reduced := R.reduced _ hred
    family := ∅
    pairwise := by intro a ha; simp at ha }
  exact exists_legallyDistinguished_of_seed S R.label_admissible

/-- Changing only the selected family leaves label eligibility intact. -/
def LegallyDistinguishedGeometricFamily.toDistinguishedFamily
    (S : LegallyDistinguishedGeometricFamily D E eps Delta) :
    EstimatingSelection.DistinguishedFamily
      (GeometricCandidate.Compatible (D := D) (eps := eps) (Delta := S.diagram))
      GeometricCandidate.weight where
  family := S.family
  pairwise := S.pairwise
  weight_maximal := fun other hother =>
    S.weight_maximal { S.toRealizedGeometricFamily with family := other, pairwise := hother }
      S.label_admissible
  card_minimal := fun other hother heq =>
    S.card_minimal { S.toRealizedGeometricFamily with family := other, pairwise := hother }
      S.label_admissible heq

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_legallyDistinguished_of_seed
#audit_axioms GroupApproximation.GGT.VanKampen.exists_legallyDistinguishedGeometricFamily
#audit_axioms GroupApproximation.GGT.VanKampen.LegallyDistinguishedGeometricFamily.toDistinguishedFamily
