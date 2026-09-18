import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarFalse
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarOpenTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 6: corrected recognition statement and the lane reductions

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-16` (Rubin route).

The lane target `RigidPolarCharacterizationStatement` (`IsRigidPolar P ↔ P = F_U`, `U` clopen) is
FALSE (RubinPolarFalse.lean): rigid stabilisers of regular open, non-closed sets are rigid polars.
The corrected recognition half is

* `RigidPolarRecognitionStatement`: in `[[S]]` (Cantor minimal), every rigid polar `P` is `F_O`
  for some open `O`.  **UNVERIFIED** (note N6 of the cartography).  It is used only as a sufficient
  condition, never as the isolated gap.

Results:

* `rigidPolarRegularCharacterization_of_rigidPolarRecognition`: under recognition,
  `IsRigidPolar P ↔ ∃ O open with interior (closure O) = O and P = F_O`.  `⇐` is proved
  unconditionally (`isRigidPolar_rubinRigidSubgroup_of_regular`).  For `⇒`, `P = C(C P)` with
  `P = F_O` gives `F_O = F_{interior (closure O)}`, and `regOpen_rigid_subset_iff` turns this into
  `O = interior (closure O)`.
* `rigidPolarOpenTransport_of_rigidPolarRecognition`: `F_U` (`U` clopen) is a rigid polar, rigid
  polars are invariant under `Φ` (`isRigidPolar_rubinTransport`), so `Φ F_U` is some `F_O`.
* `rigidStabilizerTransport_of_rigidPolarRecognition` (corrected lane reduction), and the literal
  (vacuous, since its hypothesis is false) `rigidStabilizerTransport_of_rigidPolarCharacterization`.

The TRUE isolated gap of this lane is `RigidPolarOpenTransportStatement`
(RubinPolarOpenTransport.lean).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Corrected `⇒` half of the lane characterisation: every rigid polar of `[[S]]` is the rigid
stabiliser of an open set.  UNVERIFIED; only used as a sufficient condition. -/
def RigidPolarRecognitionStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [PerfectSpace Y] [Nonempty Y] [TopologicalSpace.MetrizableSpace Y] (S : Y ≃ₜ Y),
    IsMinimalHomeo S → ∀ P : Subgroup (topologicalFullGroup S),
      IsRigidPolar P → ∃ O : Set Y, IsOpen O ∧ P = rubinRigidSubgroup S O

/-- Under recognition, rigid polars are exactly the rigid stabilisers of regular open sets. -/
theorem rigidPolarRegularCharacterization_of_rigidPolarRecognition
    (h : RigidPolarRecognitionStatement) {Y : Type} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {S : Y ≃ₜ Y} (hS : IsMinimalHomeo S)
    (P : Subgroup (topologicalFullGroup S)) :
    IsRigidPolar P ↔
      ∃ O : Set Y, IsOpen O ∧ interior (closure O) = O ∧ P = rubinRigidSubgroup S O := by
  constructor
  · intro hP
    obtain ⟨O, hO, rfl⟩ := h Y S hS P hP
    obtain ⟨hcc, -, -, -⟩ := hP
    have hc1 : Subgroup.centralizer (rubinRigidSubgroup S O : Set (topologicalFullGroup S)) =
        rubinRigidSubgroup S (closure O)ᶜ := by
      rw [centralizer_rubinRigidSubgroup hS hO, rubinRigidSubgroup_compl_eq_compl_closure S O]
    rw [hc1, centralizer_rubinRigidSubgroup hS (isClosed_closure (s := O)).isOpen_compl,
      compl_compl, ← rubinRigidSubgroup_interior (T := S) (S := closure O)] at hcc
    refine ⟨O, hO, Set.Subset.antisymm ?_ (interior_maximal subset_closure hO), rfl⟩
    refine (regOpen_rigid_subset_iff hS (isOpen_interior : IsOpen (interior (closure O)))).1 ?_
    intro k hk
    have hk' : k ∈ rubinRigidSubgroup S (interior (closure O)) := hk
    rw [← hcc] at hk'
    exact mem_rubinRigidSubgroup.1 hk'
  · rintro ⟨O, hO, hreg, rfl⟩
    exact isRigidPolar_rubinRigidSubgroup_of_regular hS hO hreg

/-- Recognition of rigid polars implies the open transport of rigid stabilisers. -/
theorem rigidPolarOpenTransport_of_rigidPolarRecognition (h : RigidPolarRecognitionStatement) :
    RigidPolarOpenTransportStatement :=
  fun _ Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU =>
    h Y S hS (rubinTransport Φ (rubinRigidSubgroup T U))
      (isRigidPolar_rubinTransport Φ (isRigidPolar_rubinRigidSubgroup_of_isClopen hT hU))

/-- Corrected lane reduction: recognition of rigid polars implies the transport of clopen rigid
stabilisers. -/
theorem rigidStabilizerTransport_of_rigidPolarRecognition (h : RigidPolarRecognitionStatement) :
    RigidStabilizerTransportStatement :=
  rigidStabilizerTransport_of_rigidPolarOpenTransport
    (rigidPolarOpenTransport_of_rigidPolarRecognition h)

/-- The (false) lane characterisation implies the recognition statement. -/
theorem rigidPolarRecognition_of_rigidPolarCharacterization
    (h : RigidPolarCharacterizationStatement) : RigidPolarRecognitionStatement :=
  fun Y _ _ _ _ _ _ _ S hS P hP => by
    obtain ⟨U, hU, hPU⟩ := (h Y S hS P).1 hP
    exact ⟨U, hU.isOpen, SetLike.coe_injective hPU⟩

/-- Literal lane reduction.  Its hypothesis is FALSE (RubinPolarFalse.lean), so this is recorded
only for the interface; use `rigidStabilizerTransport_of_rigidPolarOpenTransport` instead. -/
theorem rigidStabilizerTransport_of_rigidPolarCharacterization
    (h : RigidPolarCharacterizationStatement) : RigidStabilizerTransportStatement :=
  rigidStabilizerTransport_of_rigidPolarRecognition
    (rigidPolarRecognition_of_rigidPolarCharacterization h)

/-- The printed converse for topological full groups, reduced to the recognition of rigid
polars. -/
theorem manuscriptSentence_flipConjugateConverse_of_rigidPolarRecognition
    (h : RigidPolarRecognitionStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidPolarOpenTransport
    (rigidPolarOpenTransport_of_rigidPolarRecognition h) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidPolarRecognitionStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarRegularCharacterization_of_rigidPolarRecognition
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarOpenTransport_of_rigidPolarRecognition
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerTransport_of_rigidPolarRecognition
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarRecognition_of_rigidPolarCharacterization
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerTransport_of_rigidPolarCharacterization
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rigidPolarRecognition
