import GroupApproximation.CharClass.BundleGysinPieces

/-!
# Complex vector bundles in the projection model, XXXII: `P(p)` as a subset of
`P(p ⊕ 1)`

`projIncl` presents the hyperplane at infinity as a **map**.  A relative-cohomology
argument comparing two subspaces of one ambient needs it as a **subset**, with the
comparison map being the subset inclusion rather than a map that happens to be
injective.

The homeomorphism onto the range assembles three facts already in the lane:
`projIncl` is injective, its range is closed, and `P(p)` is compact when the base
is.  The identification then says the subset inclusion of that range into the
complement of the zero section is `projInclNotZero`, which is what lets a
consumer inherit `notZeroOpensHomotopyEquivProj_invFun` and conclude the
inclusion is a homotopy equivalence.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section ProjInclRange

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **`P(p)` is homeomorphic to its image in `P(p ⊕ 1)`.**  A continuous
injection from a compact space to a Hausdorff one. -/
noncomputable def projInclHomeoRange [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    Proj p ≃ₜ ↥(Set.range (projIncl p)) :=
  (isClosedEmbedding_projIncl p).toIsEmbedding.toHomeomorph

omit [DecidableEq ι] in
theorem projInclHomeoRange_coe [CompactSpace X] [T2Space X] (p : Bundle X ι) (z : Proj p) :
    ((projInclHomeoRange p z : Proj p.plusOne)) = projIncl p z := rfl

/-- **The hyperplane at infinity misses the zero section.** -/
theorem range_projIncl_subset_notZeroOpensSet (p : Bundle X ι) :
    Set.range (projIncl p) ⊆ notZeroOpensSet p := by
  rintro z ⟨w, rfl⟩
  exact (projIncl_mem_notZeroSet p w).2

/-- **The subset inclusion is `projInclNotZero`.**  By `rfl`, so a consumer can
transport `notZeroOpensHomotopyEquivProj_invFun` across it with no congruence
step. -/
theorem inclusion_projInclHomeoRange [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (z : Proj p) :
    Set.inclusion (range_projIncl_subset_notZeroOpensSet p) (projInclHomeoRange p z)
      = notZeroHomeoOpens p (projInclNotZero p z) := rfl

end ProjInclRange

end Bundle

end CharClass
end GroupApproximation
