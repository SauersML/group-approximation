import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Locally finite groups

A group is *locally finite* when every finite subset lies in a finite
subgroup. This file defines the project-local predicate and records its
pullback along an injective homomorphism.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-! ## The local finiteness predicate -/

/-- A group is locally finite when every finite subset lies in a finite
subgroup.  Mathlib has no such predicate for groups, so it is spelled out
here in the form the approximation arguments consume. -/
def IsLocallyFiniteGroup (G : Type u) [Group G] : Prop :=
  ∀ s : Finset G, ∃ H : Subgroup G, Finite H ∧ ∀ g ∈ s, g ∈ H

/-- Local finiteness passes to subgroups of the ambient group: intersect a
witnessing finite subgroup with the image of the smaller group. -/
theorem IsLocallyFiniteGroup.comap {H : Type*} [Group H]
    (hG : IsLocallyFiniteGroup G) (ι : H →* G) (hι : Function.Injective ι) :
    IsLocallyFiniteGroup H := by
  classical
  intro s
  obtain ⟨K, hKfin, hsK⟩ := hG (s.image ι)
  refine ⟨K.comap ι, ?_, fun g hg ↦ hsK (ι g) (Finset.mem_image_of_mem ι hg)⟩
  exact Finite.of_injective (fun x : K.comap ι ↦ (⟨ι x.1, x.2⟩ : K))
    (fun x y hxy ↦ Subtype.ext (hι (congrArg Subtype.val hxy)))

end GroupApproximation
