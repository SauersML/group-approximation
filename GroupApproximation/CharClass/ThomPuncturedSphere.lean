import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible

/-!
# A punctured sphere is contractible

The first base case of the punctured-product recursion (`ThomPuncturedRecursion.lean`)
is `S^n ∖ pt ≃ pt` for `n ≥ 1`.  This file supplies it, for the unit sphere of an
arbitrary real inner product space — so it covers `S¹`, `S⁴ ⊂ ℝ⁵` and
`S⁵ ⊂ ℂ³` in whatever concrete guise the C*-side lanes use them, as long as the
model is `Metric.sphere (0 : E) 1`.

The proof is stereographic projection: Mathlib's `stereographic` is an open partial
homeomorphism from the unit sphere to the orthogonal complement `(ℝ ∙ v)ᗮ`, with source
the complement of `v` and target everything.  A real topological vector space is
contractible (`RealTopologicalVectorSpace.contractibleSpace`), and contractibility
transports along a homeomorphism.

Nothing here is dimension-dependent, and nothing here needs a peer lane.
-/

namespace GroupApproximation.CharClass

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The source of the stereographic projection centred at `v` is the complement of `v`.
(Mathlib states it with the point spelled `⟨↑v, _⟩`; `Subtype.coe_eta` closes the gap.) -/
theorem stereographic_source_eq_compl (v : sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere v)).source
      = ({v}ᶜ : Set ↥(sphere (0 : E) 1)) := by
  simp

/-- **Stereographic projection identifies a punctured sphere with a real vector space.**
The vector space is the orthogonal complement of the puncture. -/
def spherePuncturedHomeo (v : sphere (0 : E) 1) :
    ↥({v}ᶜ : Set ↥(sphere (0 : E) 1)) ≃ₜ ↥((ℝ ∙ (v : E))ᗮ) :=
  (Homeomorph.setCongr (stereographic_source_eq_compl v).symm).trans
    ((stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic_target (norm_eq_of_mem_sphere v))).trans
        (Homeomorph.Set.univ _)))

/-- **A punctured sphere is contractible.**  This is the base case `S^n ∖ pt ≃ pt` of the
punctured-product recursion; combined with `H^k(S^n; F₂) = 0` for `k > n` it gives
`PuncturedAcyclic ↥(sphere (0 : E) 1) n v` through
`puncturedAcyclic_of_contractible`. -/
instance contractibleSpace_sphere_compl (v : sphere (0 : E) 1) :
    ContractibleSpace ↥({v}ᶜ : Set ↥(sphere (0 : E) 1)) :=
  (spherePuncturedHomeo v).contractibleSpace

end GroupApproximation.CharClass
