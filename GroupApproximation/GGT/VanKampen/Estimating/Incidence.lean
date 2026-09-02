import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# The estimating graph of an embedded distinguished family

This file constructs the finite incidence graph used in Osin's Appendix.
Its edges are precisely the selected cell-to-cell embedded contiguity
regions.  Each edge has its stored source and target as its only possible
endpoints, so edge coverage and the two-endpoint property are automatic.

The final estimates transfer Lemma O52 from the embedded region equations to
both endpoints.  Planarity, simplicity, and the equality between positioned
interior darts and edge weights are kept as the geometric conclusions of
Lemma 65(a), rather than included in the finite incidence construction.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

/-- A selected cell-to-cell region, represented together with the target
cell which its dependent `Option` field names. -/
def InteriorEdge
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :=
  { pair : Candidate D eps Delta × Fin Delta.rCellCount //
      pair.1 ∈ selected ∧ pair.1.contiguity.target = some pair.2 }

noncomputable instance interiorEdgeFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    Fintype (InteriorEdge selected) := by
  classical
  letI : Finite (InteriorEdge selected) :=
    Finite.of_injective (fun edge : InteriorEdge selected => edge.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance interiorEdgeDecidableEq
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    DecidableEq (InteriorEdge selected) :=
  Classical.decEq _

namespace InteriorEdge

/-- The selected candidate underlying an estimating edge. -/
def candidate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) : Candidate D eps Delta :=
  edge.1.1

/-- The target relator cell of an estimating edge. -/
def target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) : Fin Delta.rCellCount :=
  edge.1.2

/-- The underlying candidate belongs to the distinguished family. -/
theorem candidate_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) : edge.candidate ∈ selected :=
  edge.2.1

/-- The stored target equation for the underlying embedded region. -/
theorem target_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) :
    edge.candidate.contiguity.target = some edge.target :=
  edge.2.2

/-- A relator cell is incident to an estimating edge when it is the source
or the target of the corresponding embedded region. -/
def Incident
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (cellIndex : Fin Delta.rCellCount) (edge : InteriorEdge selected) : Prop :=
  edge.candidate.contiguity.source = cellIndex ∨ edge.target = cellIndex

noncomputable instance incidentDecidable
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    DecidableRel (Incident (selected := selected)) :=
  fun _ _ => Classical.propDecidable _

/-- Every estimating edge is covered by its source cell. -/
theorem edgesCovered_univ
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    EdgesCovered (Incident (selected := selected)) Finset.univ Finset.univ := by
  intro edge _
  exact ⟨edge.candidate.contiguity.source, Finset.mem_univ _, Or.inl rfl⟩

/-- An estimating edge has no incident vertices other than its stored source
and target. -/
theorem hasAtMostTwoEndpoints
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    HasAtMostTwoEndpoints (Incident (selected := selected)) := by
  classical
  intro vertices edge
  have hsubset :
      (vertices.filter fun i => Incident i edge) ⊆
        {edge.candidate.contiguity.source, edge.target} := by
    intro i hi
    have hincident : Incident i edge := (Finset.mem_filter.mp hi).2
    rcases hincident with hsource | htarget
    · simp [hsource]
    · simp [htarget]
  exact le_trans (Finset.card_le_card hsubset) Finset.card_le_two

/-- Natural edge weight: the sum of its two contiguity-arc lengths. -/
noncomputable def weight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (edge : InteriorEdge selected) : ℝ :=
  edge.candidate.weight

/-- The face-set equations for every interior edge give the O52 charge at
each incident endpoint. -/
theorem weight_le_incident
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (equations : ∀ edge : InteriorEdge selected,
      CellPieceEquations edge.candidate.contiguity)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (i : Fin Delta.rCellCount) (edge : InteriorEdge selected)
    (hincident : Incident i edge) :
    edge.weight ≤ 2 * mu * ((cell Delta i).word.length : ℝ) := by
  rcases hincident with hsource | htarget
  · rw [← hsource]
    exact edge.candidate.weight_le_two_mu_source (equations edge)
      hcondition.toIsSmallCancellation hcondition.publishedPiecesSmall
  · rw [← htarget]
    have hequationTarget : (equations edge).target = edge.target := by
      have hfirst := (equations edge).target_eq
      have hsecond := edge.target_eq
      rw [hsecond] at hfirst
      exact (Option.some.inj hfirst).symm
    rw [← hequationTarget]
    exact edge.candidate.weight_le_two_mu_target (equations edge)
      hcondition.toIsSmallCancellation hcondition.publishedPiecesSmall

end InteriorEdge

/-! ## Reindexing all interior cell occurrences -/

/-- All cellwise interior incidences of a selected family. -/
noncomputable def InteriorIncidence
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :=
  Σ i : Fin Delta.rCellCount,
    CellIncidence.OfKind (selected := selected) (i := i) CellArcKind.interior

noncomputable instance interiorIncidenceFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)} :
    Fintype (InteriorIncidence selected) := by
  unfold InteriorIncidence
  infer_instance

/-- Send a cellwise interior incidence to its selected cell-to-cell region and
the Boolean which distinguishes its source and target occurrences. -/
noncomputable def interiorIncidenceToTagged
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    InteriorIncidence selected → InteriorEdge selected × Bool := by
  intro occurrence
  obtain ⟨i, incidence, hkind⟩ := occurrence
  cases incidence with
  | source candidate mem_selected source_eq =>
      cases htarget : candidate.contiguity.target with
      | none =>
          have hfalse : CellArcKind.exterior = CellArcKind.interior := by
            simpa only [CellIncidence.kind, htarget, ↓reduceIte] using hkind
          cases hfalse
      | some target =>
          exact (⟨(candidate, target), mem_selected, htarget⟩, false)
  | target candidate mem_selected target_eq =>
      exact (⟨(candidate, i), mem_selected, target_eq⟩, true)

/-- Recover the source or target occurrence selected by a tagged interior
edge. -/
noncomputable def taggedToInteriorIncidence
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    InteriorEdge selected × Bool → InteriorIncidence selected
  | (edge, false) =>
      ⟨edge.candidate.contiguity.source,
        ⟨CellIncidence.source edge.candidate edge.candidate_mem rfl,
          by simp [CellIncidence.kind, edge.target_eq]⟩⟩
  | (edge, true) =>
      ⟨edge.target,
        ⟨CellIncidence.target edge.candidate edge.candidate_mem edge.target_eq,
          rfl⟩⟩

/-- The forward map sends the source occurrence to the false tag. -/
theorem interiorIncidenceToTagged_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (candidate : Candidate D eps Delta) (mem_selected : candidate ∈ selected)
    (target : Fin Delta.rCellCount)
    (htarget : candidate.contiguity.target = some target) :
    interiorIncidenceToTagged selected
        ⟨candidate.contiguity.source,
          ⟨CellIncidence.source candidate mem_selected rfl,
            by simp [CellIncidence.kind, htarget]⟩⟩ =
      (⟨(candidate, target), mem_selected, htarget⟩, false) := by
  unfold interiorIncidenceToTagged
  cases htarget
  rfl

/-- The forward map sends the target occurrence to the true tag. -/
theorem interiorIncidenceToTagged_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (candidate : Candidate D eps Delta) (mem_selected : candidate ∈ selected)
    (target : Fin Delta.rCellCount)
    (htarget : candidate.contiguity.target = some target) :
    interiorIncidenceToTagged selected
        ⟨target,
          ⟨CellIncidence.target candidate mem_selected htarget, rfl⟩⟩ =
      (⟨(candidate, target), mem_selected, htarget⟩, true) := by
  unfold interiorIncidenceToTagged
  rfl

/-- Recovering an interior incidence after tagging it is the identity. -/
theorem taggedToInteriorIncidence_leftInverse
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    Function.LeftInverse (taggedToInteriorIncidence selected)
      (interiorIncidenceToTagged selected) := by
  intro occurrence
  obtain ⟨i, incidence, hkind⟩ := occurrence
  cases incidence with
  | source candidate mem_selected source_eq =>
      cases htarget : candidate.contiguity.target with
      | none =>
          have hfalse : CellArcKind.exterior = CellArcKind.interior := by
            simpa only [CellIncidence.kind, htarget, ↓reduceIte] using hkind
          cases hfalse
      | some target =>
          cases source_eq
          rw [interiorIncidenceToTagged_source selected candidate mem_selected
            target htarget]
          unfold taggedToInteriorIncidence
          rfl
  | target candidate mem_selected target_eq =>
      rw [interiorIncidenceToTagged_target selected candidate mem_selected i
        target_eq]
      unfold taggedToInteriorIncidence
      rfl

/-- Tagging a recovered endpoint occurrence is the identity. -/
theorem taggedToInteriorIncidence_rightInverse
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    Function.RightInverse (taggedToInteriorIncidence selected)
      (interiorIncidenceToTagged selected) := by
  rintro ⟨edge, tag⟩
  cases tag with
  | false =>
      unfold taggedToInteriorIncidence
      rw [interiorIncidenceToTagged_source selected edge.candidate
        edge.candidate_mem edge.target edge.target_eq]
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl
  | true =>
      unfold taggedToInteriorIncidence
      rw [interiorIncidenceToTagged_target selected edge.candidate
        edge.candidate_mem edge.target edge.target_eq]
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl

/-- Every selected cell-to-cell region occurs exactly twice in the cellwise
interior incidence sum, once at its source and once at its target. -/
noncomputable def interiorIncidenceEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    InteriorIncidence selected ≃ InteriorEdge selected × Bool where
  toFun := interiorIncidenceToTagged selected
  invFun := taggedToInteriorIncidence selected
  left_inv := taggedToInteriorIncidence_leftInverse selected
  right_inv := taggedToInteriorIncidence_rightInverse selected

/-! ## Exterior regions -/

/-- A selected region from one fixed relator cell to the outer boundary. -/
def ExteriorRegion
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) :=
  { candidate : Candidate D eps Delta //
      candidate ∈ selected ∧
        candidate.contiguity.source = i ∧
        candidate.contiguity.target = none }

noncomputable instance exteriorRegionFintype
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount} : Fintype (ExteriorRegion selected i) := by
  classical
  letI : Finite (ExteriorRegion selected i) :=
    Finite.of_injective
      (fun region : ExteriorRegion selected i => region.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

namespace ExteriorRegion

/-- Forget the selected-family membership while retaining the embedded
boundary-contiguity witness. -/
noncomputable def toBoundaryContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (region : ExteriorRegion selected i) :
    EmbeddedBoundaryContiguity D eps Delta i where
  faces := region.1.1
  region := region.1.contiguity
  source_eq := region.2.2.1
  target_eq := region.2.2.2

end ExteriorRegion

/-- Choose one selected exterior region at a cell when such a region exists.
Lemma 65(a)'s two-gon condition later shows that this one region accounts for
the entire exterior class. -/
noncomputable def selectedOuter
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) :
    Option (EmbeddedBoundaryContiguity D eps Delta i) := by
  classical
  exact if h : Nonempty (ExteriorRegion selected i) then
    some (Classical.choice h).toBoundaryContiguity
  else none

/-- The canonical exterior option is absent exactly when no selected region
joins the cell to the outer boundary. -/
theorem selectedOuter_eq_none_iff
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) :
    selectedOuter selected i = none ↔ IsEmpty (ExteriorRegion selected i) := by
  classical
  rw [selectedOuter]
  split_ifs with h
  · simp only [false_iff]
    intro hEmpty
    letI : IsEmpty (ExteriorRegion selected i) := hEmpty
    exact isEmptyElim (Classical.choice h)
  · simp only [true_iff]
    exact ⟨fun region => h ⟨region⟩⟩

end Embedded

end VanKampen
end GGT
end GroupApproximation
