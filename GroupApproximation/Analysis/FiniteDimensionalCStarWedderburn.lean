import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Algebraic Wedderburn decomposition of finite-dimensional C-star algebras

This file discharges the algebraic part of the finite-dimensional structure
theorem.  A finite-dimensional complex C-star algebra has zero Jacobson
radical: the radical is nilpotent, while a nilpotent two-sided ideal in a
C-star algebra is zero by applying the C-star identity to `star a * a`.
Artin--Wedderburn over the algebraically closed field `ℂ` then gives an
algebra equivalence with a finite product of full matrix algebras.

The remaining analytic step is to replace the resulting algebra equivalence
by a star-algebra equivalence.  That upgrade is not encoded as an assumption
here.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A central idempotent in a C-star algebra is a projection.  In
particular, the involution fixes the central block idempotents in an
Artin--Wedderburn decomposition, so it cannot permute distinct simple
summands. -/
theorem isSelfAdjoint_of_mem_center_of_isIdempotentElem
    {D : Type*} [CStarAlgebra D] {p : D}
    (hpCenter : p ∈ Subring.center D) (hp : IsIdempotentElem p) :
    IsSelfAdjoint p := by
  apply hp.isSelfAdjoint_iff_isStarNormal.mpr
  exact ⟨Subring.mem_center_iff.mp hpCenter (star p)⟩

/-- Transporting the involution through any algebra equivalence fixes every
central idempotent of the target.  Applied to the coordinate identities of an
Artin--Wedderburn product, this shows that the transported involution
preserves each matrix block separately. -/
theorem algEquiv_transport_star_fixes_central_idempotent
    {D B : Type*} [CStarAlgebra D] [Ring B] [Algebra ℂ B]
    (e : D ≃ₐ[ℂ] B) {z : B}
    (hzCenter : z ∈ Subring.center B) (hz : IsIdempotentElem z) :
    e (star (e.symm z)) = z := by
  have hpCenter : e.symm z ∈ Subring.center D := by
    exact (MulEquivClass.apply_mem_center_iff e.symm).mpr hzCenter
  have hpSelf : IsSelfAdjoint (e.symm z) :=
    isSelfAdjoint_of_mem_center_of_isIdempotentElem hpCenter (hz.map e.symm)
  calc
    e (star (e.symm z)) = e (e.symm z) := congrArg e hpSelf
    _ = z := e.apply_symm_apply z

/-- A nilpotent two-sided ideal in a C-star algebra is zero. -/
theorem nilpotent_ideal_eq_bot_of_cstar
    {D : Type*} [CStarAlgebra D] (J : Ideal D) [J.IsTwoSided]
    (hJ : IsNilpotent J) : J = ⊥ := by
  apply le_antisymm
  · intro a ha
    obtain ⟨n, hn⟩ := hJ
    let b : D := star a * a
    have hbJ : b ∈ J := J.mul_mem_left (star a) ha
    have hbpow_mem : b ^ n ∈ J ^ n := Ideal.pow_mem_pow hbJ n
    have hbpow : b ^ n = 0 := by
      rw [hn] at hbpow_mem
      simpa only [Ideal.mem_bot] using hbpow_mem
    have hlarge : n ≤ 2 ^ n := n.lt_two_pow_self.le
    have hbpowTwo : b ^ (2 ^ n) = 0 := pow_eq_zero_of_le hlarge hbpow
    have hbself : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
    have hnormpow := hbself.norm_pow_two_pow n
    rw [hbpowTwo, norm_zero] at hnormpow
    have hnormb : ‖b‖ = 0 :=
      (pow_eq_zero_iff (by positivity : (2 : ℕ) ^ n ≠ 0)).mp hnormpow.symm
    have hbzero : b = 0 := norm_eq_zero.mp hnormb
    exact (CStarRing.star_mul_self_eq_zero_iff a).mp hbzero
  · exact bot_le

/-- A finite-dimensional complex C-star algebra has zero Jacobson radical. -/
theorem finiteDimensionalCStar_jacobson_eq_bot
    (D : Type*) [CStarAlgebra D] [FiniteDimensional ℂ D] :
    Ring.jacobson D = ⊥ := by
  letI : IsArtinianRing D := IsArtinianRing.of_finite ℂ D
  exact nilpotent_ideal_eq_bot_of_cstar (Ring.jacobson D)
    IsArtinianRing.isNilpotent_jacobson_bot

/-- Every finite-dimensional complex C-star algebra is semisimple as a ring. -/
theorem finiteDimensionalCStar_isSemisimpleRing
    (D : Type*) [CStarAlgebra D] [FiniteDimensional ℂ D] :
    IsSemisimpleRing D := by
  letI : IsArtinianRing D := IsArtinianRing.of_finite ℂ D
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
    (finiteDimensionalCStar_jacobson_eq_bot D)

/-- The unconditional algebraic Artin--Wedderburn decomposition of a
finite-dimensional complex C-star algebra. -/
theorem exists_algEquiv_directMatrixSum_of_finiteDimensionalCStar
    (D : Type*) [CStarAlgebra D] [FiniteDimensional ℂ D] :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (D ≃ₐ[ℂ] DirectMatrixSum d) := by
  letI : IsSemisimpleRing D := finiteDimensionalCStar_isSemisimpleRing D
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ D

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms nilpotent_ideal_eq_bot_of_cstar
#audit_axioms isSelfAdjoint_of_mem_center_of_isIdempotentElem
#audit_axioms algEquiv_transport_star_fixes_central_idempotent
#audit_axioms finiteDimensionalCStar_isSemisimpleRing
#audit_axioms exists_algEquiv_directMatrixSum_of_finiteDimensionalCStar
