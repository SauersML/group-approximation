import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Sofic.KazhdanCompressionFunctorial

/-!
# The quotient-property-(T) end of defect saturation

The final image clause in the proof of `prop:defect-saturation` first passes
property `(T)` to `f(L)` and `Q`, then applies the compression criterion in
`Q` with `K = Q`.  This file exposes those exact steps.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

section

variable {G Q : Type} [Group G] [Group Q]

/-- Property `(T)` of the manuscript subgroup passes to its mapped subgroup. -/
theorem manuscriptMappedSubgroupHasKazhdanPropertyT
    (f : G →* Q) (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    HasKazhdanPropertyT.{0, 0} ↥(L.map f) :=
  KazhdanCompressionCore.map_subgroup_hasKazhdanPropertyT L f hL

/-- A surjective image of the ambient Kazhdan group is Kazhdan. -/
theorem manuscriptSurjectiveImageHasKazhdanPropertyT
    (f : G →* Q) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT.{0, 0} G) :
    HasKazhdanPropertyT.{0, 0} Q :=
  HasKazhdanPropertyT.of_surjective f hf hG

/-- With the mapped defect already full, the compression criterion applied
inside `Q`, with normal Kazhdan subgroup `K = Q`, makes the MF radical of
`Q` full. -/
theorem manuscriptMappedFullDefectGivesFullMFRadical
    [Countable G] (f : G →* Q) (hf : Function.Surjective f)
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hD : printedDefect (L.map f) = ⊤) :
    manuscriptCoronaMFResidual Q = ⊤ := by
  letI : Countable Q := Function.Surjective.countable hf
  exact
    (manuscriptOneSidedCompressionCriterion Q (L.map f)
      (manuscriptMappedSubgroupHasKazhdanPropertyT f L hL)).2.2
      (manuscriptSurjectiveImageHasKazhdanPropertyT f hf hG) hD

/-- **The final image route in the proof around census rows 199--200.**
All printed hypotheses are retained.  The conclusion exposes property `(T)`
for `f(L)` and `Q`, fullness of the mapped defect, and the final full-radical
conclusion obtained by taking `K = Q` in the compression criterion. -/
theorem manuscriptImageSaturationFullMFRadicalRoute
    [Countable G] (f : G →* Q) (hf : Function.Surjective f)
    (L S : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hS : IsSimpleGroup S) (hSD : S ≤ printedDefect L)
    (hne : S.map f ≠ ⊥)
    (hgen : Subgroup.normalClosure (S.map f : Set Q) = ⊤) :
    HasKazhdanPropertyT.{0, 0} ↥(L.map f) ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      printedDefect (L.map f) = ⊤ ∧
      manuscriptCoronaMFResidual Q = ⊤ := by
  have hLT := manuscriptMappedSubgroupHasKazhdanPropertyT f L hL
  have hQT := manuscriptSurjectiveImageHasKazhdanPropertyT f hf hG
  have hD := printedDefect_map_eq_top_of_simple_image_normalClosure_eq_top
    f hf L S hS hSD hne hgen
  exact ⟨hLT, hQT, hD,
    manuscriptMappedFullDefectGivesFullMFRadical f hf L hL hG hD⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
