import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# Operator-algebraic consequences of the compression mechanism

The reduced side is unconditional: the concrete reduced group C⋆-algebra
constructed in `ReducedGroupCStarTrace` has its canonical faithful trace, so
all finite matrix amplifications are finite.

Mathlib currently has no maximal group C⋆-algebra API.  Accordingly, the
maximal-side result below does not introduce a fictitious one.  It accepts an
explicit injective star-algebra homomorphism (the paper supplies this from a
subgroup inclusion/universal property) and proper projection-compression data
in its source.  Injectivity preserves properness, producing the advertised
proper isometry in the target C⋆-algebra.
-/

namespace GroupApproximation

noncomputable section

universe u v

/-- Explicit data for an injective unital star-algebra map between complex
C⋆-algebras.  In the group-algebra application this is the map induced by an
injective subgroup homomorphism; that literature input is kept visible rather
than hidden behind a nonexistent maximal-group-C⋆ API. -/
structure InjectiveCStarEmbedding (A : Type u) (B : Type v)
    [CStarAlgebra A] [CStarAlgebra B] where
  /-- The specified unital star-algebra map. -/
  hom : A →⋆ₐ[ℂ] B
  /-- Faithfulness of the specified map. -/
  injective : Function.Injective hom

namespace InjectiveCStarEmbedding

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- Proper projection-compression data transports through an injective
star-algebra map. -/
def mapCompression (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) : ProperProjectionCompression B where
  p := e.hom D.p
  u := e.hom D.u
  p_star := by rw [← map_star, D.p_star]
  p_mul_p := by rw [← map_mul, D.p_mul_p]
  u_star_mul := by rw [← map_star, ← map_mul, D.u_star_mul, map_one]
  u_mul_star := by rw [← map_star, ← map_mul, D.u_mul_star, map_one]
  p_mul_conjugate := by
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul,
      D.p_mul_conjugate]
  conjugate_mul_p := by
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul,
      D.conjugate_mul_p]
  conjugate_ne := by
    intro h
    apply D.conjugate_ne
    apply e.injective
    simpa only [map_mul, map_star] using h

/-- An injective image of proper compression data contains an explicit proper
isometry. -/
def properIsometry (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) : B :=
  (e.mapCompression D).isometry

/-- The image isometry is left-unitary but not right-unitary. -/
theorem properIsometry_spec (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) :
    star (e.properIsometry D) * e.properIsometry D = 1 ∧
      e.properIsometry D * star (e.properIsometry D) ≠ 1 :=
  (e.mapCompression D).star_isometry_mul_eq_one_and_reverse_ne

/-- Hence the target algebra is not directly finite. -/
theorem target_not_isDedekindFiniteMonoid
    (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) :
    ¬ IsDedekindFiniteMonoid B :=
  (e.mapCompression D).not_isDedekindFiniteMonoid

/-- Hence the target algebra is not stably finite. -/
theorem target_not_isStablyFiniteRing
    (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) :
    ¬ IsStablyFiniteRing B :=
  (e.mapCompression D).not_isStablyFiniteRing

/-- A target containing the injected compression cannot carry a faithful
tracial state. -/
theorem target_no_faithfulTracialState
    (e : InjectiveCStarEmbedding A B)
    (D : ProperProjectionCompression A) :
    ¬ Nonempty (FaithfulTracialState B) :=
  (e.mapCompression D).no_faithfulTracialState

end InjectiveCStarEmbedding

namespace ReducedGroupCStarTrace

universe w

variable (G : Type w) [Group G]

/-- Every isometry in every nonempty finite matrix amplification of the
reduced group C⋆-algebra is unitary.  This is the operator-algebraic stable
finiteness conclusion furnished by the canonical faithful trace. -/
theorem reduced_matrix_mul_star_eq_one_of_star_mul_eq_one
    (n : Type*) [Fintype n] [DecidableEq n] (hn : Nonempty n)
    {v : CStarMatrix n n (ReducedGroupCStar G)}
    (hv : star v * v = 1) : v * star v = 1 :=
  (canonicalFaithfulTracialState G).matrix_mul_star_eq_one_of_star_mul_eq_one
    n hn hv

/-- In particular, the reduced group C⋆-algebra itself contains no proper
isometry. -/
theorem reduced_mul_star_eq_one_of_star_mul_eq_one
    {v : ReducedGroupCStar G} (hv : star v * v = 1) :
    v * star v = 1 :=
  (canonicalFaithfulTracialState G).mul_star_eq_one_of_star_mul_eq_one hv

/-- Consequently the reduced group C⋆-algebra admits no proper projection
compression of the form used on the maximal side. -/
theorem reduced_no_properProjectionCompression :
    IsEmpty (ProperProjectionCompression (ReducedGroupCStar G)) :=
  ⟨fun D ↦ D.isometry_mul_star_ne_one
    (reduced_mul_star_eq_one_of_star_mul_eq_one G D.star_isometry_mul_isometry)⟩

end ReducedGroupCStarTrace

end


end GroupApproximation
