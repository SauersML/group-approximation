import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialRealize
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse: closing the equivalence loop of the four gap statements

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).

The corpus proves
* `SupportDisjointnessTransportStatement ↔ RigidStabilizerSplitStatement` (`RigidSplit.lean`),
* `RigidStabilizerSplitStatement → RigidStabilizerTransportStatement` (`RigidCentralizer.lean`),
* `RigidStabilizerTransportStatement → SpatialRealizationStatement` (`SpatialRealize.lean`).

This file adds the missing arrow `SpatialRealizationStatement → SupportDisjointnessTransportStatement`,
so all four statements are equivalent and any one of them closes the region.

Route (`supportDisjointnessTransport_of_spatialRealization`): if `Φ g ∘ h = h ∘ g` for a
homeomorphism `h : X ≃ₜ Y`, then `movedSet (Φ g) = h '' movedSet g`
(`movedSet_map_eq_image_of_spatiallyImplemented`), and images of disjoint sets under the
injective map `h` are disjoint (`Set.disjoint_image_iff`).  The second endpoint composes this with
`spatialRealization_of_rigidStabilizerTransport`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- A spatially implemented isomorphism moves exactly the `h`-image of the moved set. -/
theorem movedSet_map_eq_image_of_spatiallyImplemented {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) (h : X ≃ₜ Y)
    (hΦ : ∀ (g : topologicalFullGroup T) (x : X),
      ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) = h ((g : X ≃ₜ X) x))
    (g : topologicalFullGroup T) :
    movedSet ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) = h '' movedSet (g : X ≃ₜ X) := by
  ext y
  constructor
  · intro hy
    have hy' : ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) y ≠ y := hy
    refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
    show (g : X ≃ₜ X) (h.symm y) ≠ h.symm y
    intro hfix
    have e := hΦ g (h.symm y)
    rw [h.apply_symm_apply, hfix, h.apply_symm_apply] at e
    exact hy' e
  · rintro ⟨x, hx, rfl⟩
    have hx' : (g : X ≃ₜ X) x ≠ x := hx
    show ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) ≠ h x
    rw [hΦ g x]
    exact fun e => hx' (h.injective e)

/-- A spatially implemented isomorphism carries disjoint moved sets to disjoint moved sets. -/
theorem disjoint_movedSet_map_of_spatiallyImplemented {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) (h : X ≃ₜ Y)
    (hΦ : ∀ (g : topologicalFullGroup T) (x : X),
      ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) = h ((g : X ≃ₜ X) x))
    {f k : topologicalFullGroup T}
    (hfk : Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X))) :
    Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
      (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y)) := by
  rw [movedSet_map_eq_image_of_spatiallyImplemented Φ h hΦ f,
    movedSet_map_eq_image_of_spatiallyImplemented Φ h hΦ k]
  exact (Set.disjoint_image_iff h.injective).2 hfk

/-- Spatial realization implies transport of disjointness of supports. -/
theorem supportDisjointnessTransport_of_spatialRealization
    (hsr : SpatialRealizationStatement) : SupportDisjointnessTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ _ _ hfk => by
    obtain ⟨h, hh⟩ := hsr X Y T S hT hS Φ
    exact disjoint_movedSet_map_of_spatiallyImplemented Φ h hh hfk

/-- Transport of rigid stabilizers implies transport of disjointness of supports
(through spatial realization). -/
theorem supportDisjointnessTransport_of_rigidStabilizerTransport
    (hrs : RigidStabilizerTransportStatement) : SupportDisjointnessTransportStatement :=
  supportDisjointnessTransport_of_spatialRealization
    (spatialRealization_of_rigidStabilizerTransport hrs)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.movedSet_map_eq_image_of_spatiallyImplemented
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.disjoint_movedSet_map_of_spatiallyImplemented
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_spatialRealization
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_rigidStabilizerTransport
