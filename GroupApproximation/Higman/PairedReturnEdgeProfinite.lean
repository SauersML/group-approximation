import GroupApproximation.Higman.PairedReturnEdgeGraph
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# The paired-return edge as a profinitely closed graph

The first-coordinate path embeds the two-copy free product into `F₃`.  After
identifying its range with that free product, the second-coordinate path is a
homomorphism on the range.  Hence the paired-return edge is the graph of a
homomorphism, and is a retract of the product of the first-coordinate range
with `K`.

This is the intrinsic half of edge separability.  The remaining promotion
from that product to `F₃ × F₃` uses the explicit index-two virtual retraction
of the first-coordinate range.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnEdgeProfinite

open Conj
open PairedReturnEdgeGraph
open scoped Monoid.Coprod

abbrev FirstRange : Type := ↥firstPath.range

/-- The first-coordinate path identifies the two-copy free product with its
range. -/
noncomputable def doubleEquivFirstRange : Double ≃* FirstRange :=
  MulEquiv.ofBijective firstPath.rangeRestrict
    ⟨fun _ _ h => firstPath_injective (Subtype.ext_iff.mp h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The second-coordinate path, with codomain restricted to `K`. -/
def secondPathK : Double →* Sync :=
  Monoid.Coprod.lift 1 (MonoidHom.id Sync)

@[simp] theorem secondPathK_inl (h : Sync) :
    secondPathK (Monoid.Coprod.inl h) = 1 := by
  rw [secondPathK, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] theorem secondPathK_inr (h : Sync) :
    secondPathK (Monoid.Coprod.inr h) = h := by
  rw [secondPathK, Monoid.Coprod.lift_apply_inr]
  rfl

/-- The fold read in the second coordinate, now defined on the embedded
first-coordinate range. -/
noncomputable def graphFold : FirstRange →* Sync :=
  secondPathK.comp doubleEquivFirstRange.symm.toMonoidHom

/-- The graph embedding in the intrinsic product `FirstRange × K`. -/
noncomputable def graphSection : FirstRange →* FirstRange × Sync :=
  (MonoidHom.id FirstRange).prod graphFold

/-- Projection to the first coordinate retracts the graph. -/
def graphProjection : FirstRange × Sync →* FirstRange :=
  MonoidHom.fst FirstRange Sync

theorem graphProjection_comp_graphSection :
    graphProjection.comp graphSection = MonoidHom.id FirstRange := by
  ext j
  rfl

/-- The intrinsic graph is profinitely closed. -/
theorem profiniteClosure_graphSection_range :
    profiniteClosure graphSection.range = graphSection.range := by
  letI : Group.ResiduallyFinite (FirstRange × Sync) := inferInstance
  exact profiniteClosure_range_eq_range_of_retraction
    graphSection graphProjection graphProjection_comp_graphSection

end PairedReturnEdgeProfinite
end Higman
end GroupApproximation
