import GroupApproximation.GGT.VanKampen.Estimating.ContiguityFinite

/-!
# Definition M on actual contiguity data

Each candidate retains its entire geometric witness. Finite maximization now
compares every realizable pair of arc lengths, including different witnesses
on one face set. Compatibility still means disjointness of those face sets.
The historical face-only Candidate and its counterexample are preserved.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

def GeometricCandidate (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :=
  Σ faces : Finset Delta.toCombMap.Face, Contiguity D eps Delta faces

namespace GeometricCandidate

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

noncomputable instance candidateFintype : Fintype (GeometricCandidate D eps Delta) := by
  classical
  unfold GeometricCandidate
  infer_instance

def Compatible (a b : GeometricCandidate D eps Delta) : Prop := Disjoint a.1 b.1

def weight (a : GeometricCandidate D eps Delta) : ℕ :=
  a.2.sourceArc.length + a.2.targetArc.length

/-- The supplied witness is retained, so its arc weight is recovered exactly. -/
theorem weight_mk {faces : Finset Delta.toCombMap.Face} (H : Contiguity D eps Delta faces) :
    weight (⟨faces, H⟩ : GeometricCandidate D eps Delta) =
      H.sourceArc.length + H.targetArc.length := rfl

theorem exists_distinguishedFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) :
    Nonempty (EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (weight (D := D) (eps := eps) (Delta := Delta))) :=
  EstimatingSelection.exists_distinguishedFamily _ _

end GeometricCandidate
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.candidateFintype
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.weight_mk
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.exists_distinguishedFamily
