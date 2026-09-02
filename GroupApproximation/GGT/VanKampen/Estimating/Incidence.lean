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
end Embedded

end VanKampen
end GGT
end GroupApproximation
