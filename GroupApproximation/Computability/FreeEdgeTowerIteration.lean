import GroupApproximation.Computability.FreeEdgeTowerSemantics

/-!
# Iterating the raw free-edge semantics

`FreeEdgeTowerSemantics.edgeCodeEquiv` identifies one computed edge with an
honest HNN extension over the group presented at the preceding stage.  To
iterate that result, the preceding presentation equivalence has to be carried
through the next pair of associated free subgroups.  This file supplies that
transport without adding any algebraic assumption.

The only inputs retained at each stage are the two injectivity proofs for the
displayed source and target evaluations.  In particular, no MF permanence or
compiler-correctness hypothesis is hidden in the iteration layer.
-/

namespace GroupApproximation
namespace FreeEdgeTowerIteration

open HNNExtension
open Higman ExplicitFreeEdge
open HNNCongr

variable {X G H : Type} [Group G] [Group H]

/-- Transport explicitly embedded free edge groups across an equivalence of
bases. -/
def transportData (e : G ≃* H) (E : Data X G) : Data X H where
  source := e.toMonoidHom.comp E.source
  target := e.toMonoidHom.comp E.target
  source_injective := e.injective.comp E.source_injective
  target_injective := e.injective.comp E.target_injective

@[simp] theorem transportData_source (e : G ≃* H) (E : Data X G) :
    (transportData e E).source = e.toMonoidHom.comp E.source := rfl

@[simp] theorem transportData_target (e : G ≃* H) (E : Data X G) :
    (transportData e E).target = e.toMonoidHom.comp E.target := rfl

/-- An equivalence of bases carries the explicit source subgroup onto the
transported source subgroup. -/
theorem mem_sourceSubgroup_transportData_iff (e : G ≃* H) (E : Data X G)
    (g : G) :
    g ∈ sourceSubgroup E ↔ e g ∈ sourceSubgroup (transportData e E) := by
  simp only [sourceSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨w, Subgroup.mem_top w, rfl⟩
  · rintro ⟨w, -, hw⟩
    refine ⟨w, Subgroup.mem_top w, ?_⟩
    apply e.injective
    simpa [transportData] using hw

/-- Transporting the edge data preserves the canonical word-by-word edge
identification. -/
theorem transportData_intertwines (e : G ≃* H) (E : Data X G) :
    Intertwines (edgeEquiv E) (edgeEquiv (transportData e E)) e
      (mem_sourceSubgroup_transportData_iff e E) := by
  intro g hg
  let a : sourceSubgroup E := ⟨g, hg⟩
  let w : FreeGroup X := (sourceEquiv E).symm a
  have hsource : E.source w = g := by
    rw [← coe_sourceEquiv]
    change ((sourceEquiv E ((sourceEquiv E).symm a) : sourceSubgroup E) : G) = g
    rw [MulEquiv.apply_symm_apply]
    rfl
  have htransported :
      (⟨e g, (mem_sourceSubgroup_transportData_iff e E g).1 hg⟩ :
          sourceSubgroup (transportData e E)) =
        sourceElement (transportData e E) w := by
    apply Subtype.ext
    rw [coe_sourceEquiv]
    simp only [transportData_source, MonoidHom.comp_apply, hsource]
  rw [htransported]
  rw [coe_edgeEquiv_sourceElement]
  change e (E.target w) = e (((edgeEquiv E (sourceEquiv E w) :
    targetSubgroup E) : G))
  rw [coe_edgeEquiv_sourceElement]

/-- HNN extension commutes with transport of an explicitly embedded free
edge across an equivalence of bases. -/
noncomputable def transportExtensionEquiv (e : G ≃* H) (E : Data X G) :
    Extension E ≃* Extension (transportData e E) :=
  HNNCongr.congrEquiv (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E)

@[simp] theorem transportExtensionEquiv_of (e : G ≃* H) (E : Data X G)
    (g : G) :
    transportExtensionEquiv e E (of g) = of (e g) := by
  exact HNNCongr.congrHom_of (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E) g

@[simp] theorem transportExtensionEquiv_t (e : G ≃* H) (E : Data X G) :
    transportExtensionEquiv e E (t : Extension E) =
      (t : Extension (transportData e E)) := by
  exact HNNCongr.congrHom_t (edgeEquiv E) (edgeEquiv (transportData e E)) e
    (mem_sourceSubgroup_transportData_iff e E)
    (transportData_intertwines e E)

end FreeEdgeTowerIteration
end GroupApproximation
