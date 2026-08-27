import GroupApproximation.Analysis.ContinuousImageClosure
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Mapping a closed generated star algebra into a closed target
-/

namespace GroupApproximation

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
variable [TopologicalSpace A] [TopologicalSpace B]

/-- A continuous star-algebra homomorphism that sends the generators into a
closed star subalgebra sends the closure of their star algebra into that
subalgebra. -/
theorem continuous_map_mem_of_mem_closure_adjoin
    (f : A →⋆ₐ[R] B) (hf : Continuous f) (T : StarSubalgebra R B)
    (hT : IsClosed (T : Set B)) {s : Set A}
    (hgen : ∀ x ∈ s, f x ∈ T) {x : A}
    (hx : x ∈ closure (StarAlgebra.adjoin R s : Set A)) : f x ∈ T := by
  have hadjoin : StarAlgebra.adjoin R s ≤ T.comap f := by
    apply StarAlgebra.adjoin_le
    exact hgen
  exact continuous_image_closure_mem_closed f hf
    (fun y hy ↦ hadjoin hy) hT hx

end GroupApproximation
