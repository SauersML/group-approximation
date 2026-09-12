import GroupApproximation.KunThom.RelativeFunctorEstimate
import GroupApproximation.KunThom.ComponentCountingRetainedMatching

/-!
# Unmatched mass of the relative functor's bridges from the component matching

The relative cluster functor of Kun and Thom (arXiv:2608.06222v3, Lemma 4.3)
transports an arrow through the bridge realized by `u⁻¹` from a matched object
`π i` back to `i`.  Its missing mass enters estimate (7) as the error `β`.  The
component matching controls the symmetric difference `|u Q_i △ Q_{π i}|` of whole
blocks.  This file writes the missing mass of both bridges in exactly that form.

* `objectImage_image`: the translate of an object's ambient image.
* `sourceDefect_add_targetDefect_bridge_le_objectImage` and
  `sourceDefect_add_targetDefect_bridge_inv_le_objectImage`: the missing masses of
  the bridge realized by `q` from `C` to `D`, and of the bridge realized by `q⁻¹`
  from `D` to `C`, are each at most `|q Q_C △ Q_D|`.
* `sourceDefect_add_targetDefect_bridge_le_blocks` and
  `sourceDefect_add_targetDefect_bridge_inv_le_blocks`: the same bounds for
  retained objects inside whole blocks `B` and `B'`, charged to `|q B △ B'|` and
  the removed masses through `RetainedMatching.card_image_symmDiff_le`.
-/

namespace GroupApproximation
namespace RelativeFunctorEstimate

open BlockPatching FinitePartialBijection
open scoped symmDiff

universe u

variable {Y : FiniteModel} {I : Type u}

/-- The translate of the ambient image of an object is the image of its points
under the translated inclusion. -/
theorem objectImage_image (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C : I) :
    (E.objectImage C).image q = Finset.univ.image fun x : E.model C ↦ q (E.embed C x) := by
  unfold BlockEmbedding.objectImage
  exact Finset.image_image

/-- The missing masses of the bridge realized by `q` from `C` to `D` are at most
`|q Q_C △ Q_D|`. -/
theorem sourceDefect_add_targetDefect_bridge_le_objectImage (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).sourceDefect + (E.bridge q C D).targetDefect ≤
      (((E.objectImage C).image q) ∆ E.objectImage D).card := by
  rw [objectImage_image E q C]
  exact sourceDefect_add_targetDefect_bridge_le E q C D

/-- **The functor's bridge.**  The missing masses of the bridge realized by `q⁻¹`
from `D` back to `C` are at most `|q Q_C △ Q_D|`.  For the relative functor,
`q = u`, `C = i` and `D = π i`. -/
theorem sourceDefect_add_targetDefect_bridge_inv_le_objectImage (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q⁻¹ D C).sourceDefect + (E.bridge q⁻¹ D C).targetDefect ≤
      (((E.objectImage C).image q) ∆ E.objectImage D).card := by
  have h := sourceDefect_add_targetDefect_bridge_le_objectImage E q C D
  rw [sourceDefect_bridge_inv E q C D, targetDefect_bridge_inv E q C D]
  omega

/-- **Retained objects in whole blocks.**  If the objects `C` and `D` lie in blocks
`B` and `B'`, the missing masses of the bridge realized by `q` are at most
`|q B △ B'|` plus the removed masses of the two blocks. -/
theorem sourceDefect_add_targetDefect_bridge_le_blocks (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C D : I) {B B' : Finset Y}
    (hB : E.objectImage C ⊆ B) (hB' : E.objectImage D ⊆ B') :
    (E.bridge q C D).sourceDefect + (E.bridge q C D).targetDefect ≤
      ((B.image q) ∆ B').card + (B \ E.objectImage C).card + (B' \ E.objectImage D).card := by
  have h₁ := sourceDefect_add_targetDefect_bridge_le_objectImage E q C D
  have h₂ := RetainedMatching.card_image_symmDiff_le q hB hB'
  omega

/-- **The functor's bridge, from the whole-block matching.**  If the objects `C`
and `D` lie in blocks `B` and `B'`, the missing masses of the bridge realized by
`q⁻¹` from `D` back to `C` are at most `|q B △ B'|` plus the removed masses of the
two blocks. -/
theorem sourceDefect_add_targetDefect_bridge_inv_le_blocks (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C D : I) {B B' : Finset Y}
    (hB : E.objectImage C ⊆ B) (hB' : E.objectImage D ⊆ B') :
    (E.bridge q⁻¹ D C).sourceDefect + (E.bridge q⁻¹ D C).targetDefect ≤
      ((B.image q) ∆ B').card + (B \ E.objectImage C).card + (B' \ E.objectImage D).card := by
  have h₁ := sourceDefect_add_targetDefect_bridge_inv_le_objectImage E q C D
  have h₂ := RetainedMatching.card_image_symmDiff_le q hB hB'
  omega

end RelativeFunctorEstimate
end GroupApproximation
