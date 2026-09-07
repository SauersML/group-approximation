import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry

/-!
# Finite selection on unrestricted geometric contiguities

Every candidate retains its actual geometric witness, including possible
self-contiguities. Distinct-cell O52 data is not an admissibility condition.
Compatibility means disjointness of region face sets, and the optimization
weight counts both stored arc lengths. Historical candidate types remain
available separately.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

def RegionCandidate (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :=
  Σ faces : Finset Delta.toCombMap.Face, ContiguityGeometry D eps Delta faces

namespace RegionCandidate

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

noncomputable instance candidateFintype : Fintype (RegionCandidate D eps Delta) := by
  classical
  unfold RegionCandidate
  infer_instance

def Compatible (a b : RegionCandidate D eps Delta) : Prop := Disjoint a.1 b.1

def weight (a : RegionCandidate D eps Delta) : ℕ :=
  a.2.sourceArc.length + a.2.targetArc.length

/-- The supplied witness is retained, so its arc weight is recovered exactly. -/
theorem weight_mk {faces : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta faces) :
    weight (⟨faces, H⟩ : RegionCandidate D eps Delta) =
      H.sourceArc.length + H.targetArc.length := rfl

theorem exists_distinguishedFamily (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) :
    Nonempty (EstimatingSelection.DistinguishedFamily
      (Compatible (D := D) (eps := eps) (Delta := Delta))
      (weight (D := D) (eps := eps) (Delta := Delta))) :=
  EstimatingSelection.exists_distinguishedFamily _ _

end RegionCandidate
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.candidateFintype
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.weight_mk
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_distinguishedFamily
