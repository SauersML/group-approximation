import GroupApproximation.Analysis.ShulmanFillConjugatePair
import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic

/-!
# Conjugating an asymptotic lift by a unitary of `𝒟`

This is Shulman's Lemma 9 in the vocabulary that survives
`Analysis/ShulmanFillNormingResiduallyFinite`.  In the paper the decoupling
unitary of Theorem 10 has to be produced by a Halmos dilation of a
quasicentrally corrected contractive lift, because it lives in `M₄(𝒟)` and only
*converges* to the flip.  Inside `𝒟` no dilation is needed: if the flip is
already a unitary `U` of the sequence algebra, conjugation by it is an exact
operation on asymptotic lifts, and it moves the lifted representation by
`Ad (q U)`.

`StarStrongAsymptoticLift.conjugate` is that statement.  All four defects are
conjugated verbatim, so each is bounded by the corresponding defect of `φ` —
conjugation by a contraction cannot enlarge a norm — and the lifting clause
moves by the image of `U` because `q` is a unital `*`-homomorphism.

What this does *not* supply is the flip itself.  For the symmetric double the
flip is `((0,1),(1,0))` over the models, so it is a unitary of `𝒟` exactly when
the models are `M₂` over something and `H` is a twofold block space; the exact
commutation with the diagonal image of `C` is already proved in
`Analysis/ShulmanFillSymmetricDoubleFlip`
(`flip2_commutes_diagonal2_self`, `unitaryConj_flipUnitary_diagonal2`).
Building that amplified model is a separate construction task, and its only
interface with this module is the four hypotheses on `U` below.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section Conjugate

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
-- `lp _ ∞` is a unital ring only when its factors are, so the `𝒟` API now
-- carries this; `StarStrongLimitNorm` declares it the same way.
variable [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

variable (U : StarStrong.BoundedStarSequence A)
  (hUmem : U ∈ StarStrong.starStrongSubalgebra ι hnorm hone)
  (hUl : star U * U = 1) (hUr : U * star U = 1) (hU1 : ‖U‖ ≤ 1)

/-- The `*`-strong limit of the conjugating unitary. -/
def limitUnitary : H →L[ℂ] H :=
  StarStrong.starStrongLimitHom ι hnorm hone ⟨U, hUmem⟩

include hUl hUr in
/-- The limit of a unitary of `𝒟` is a unitary of `B(H)`: `q` is a unital
`*`-homomorphism, so it carries both unitarity identities across. -/
theorem limitUnitary_mem_unitary :
    limitUnitary U hUmem ∈ unitary (H →L[ℂ] H) := by
  have hUs : (⟨star U, star_mem hUmem⟩ :
      StarStrong.starStrongSubalgebra ι hnorm hone) = star ⟨U, hUmem⟩ := rfl
  constructor
  · show star (limitUnitary U hUmem) * limitUnitary U hUmem = 1
    rw [limitUnitary, ← map_star, ← hUs, ← map_mul]
    have hprod : (⟨star U, star_mem hUmem⟩ :
        StarStrong.starStrongSubalgebra ι hnorm hone) * ⟨U, hUmem⟩ = 1 :=
      Subtype.ext hUl
    rw [hprod, map_one]
  · show limitUnitary U hUmem * star (limitUnitary U hUmem) = 1
    rw [limitUnitary, ← map_star, ← hUs, ← map_mul]
    have hprod : (⟨U, hUmem⟩ :
        StarStrong.starStrongSubalgebra ι hnorm hone) *
          ⟨star U, star_mem hUmem⟩ = 1 :=
      Subtype.ext hUr
    rw [hprod, map_one]

/-- The conjugating unitary of `B(H)`, bundled. -/
def limitUnitaryBundled : unitary (H →L[ℂ] H) :=
  ⟨limitUnitary U hUmem, limitUnitary_mem_unitary U hUmem hUl hUr⟩

namespace StarStrongAsymptoticLift

omit [∀ n, Nontrivial (A n)] in
include hU1 in
/-- Conjugation by a contraction and its adjoint cannot enlarge a norm. -/
theorem norm_conj_le (x : StarStrong.BoundedStarSequence A) :
    ‖U * x * star U‖ ≤ ‖x‖ := by
  have hs : ‖star U‖ ≤ 1 := by
    rw [norm_star]
    exact hU1
  calc ‖U * x * star U‖ ≤ ‖U * x‖ * ‖star U‖ := norm_mul_le _ _
    _ ≤ (‖U‖ * ‖x‖) * ‖star U‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 := by
        refine mul_le_mul ?_ hs (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hU1 (norm_nonneg _)
    _ = ‖x‖ := by rw [one_mul, mul_one]

/-- Conjugation distributes over a two-term defect. -/
theorem conj_sub_sub (x y z : StarStrong.BoundedStarSequence A) :
    U * x * star U - U * y * star U - U * z * star U =
      U * (x - y - z) * star U := by
  rw [mul_sub, mul_sub, sub_mul, sub_mul]

/-- Conjugation distributes over a one-term defect. -/
theorem conj_sub (x y : StarStrong.BoundedStarSequence A) :
    U * x * star U - U * y * star U = U * (x - y) * star U := by
  rw [mul_sub, sub_mul]

include hUl in
/-- Conjugation is multiplicative on the nose, `star U * U = 1` cancelling in
the middle. -/
theorem conj_mul (x y : StarStrong.BoundedStarSequence A) :
    (U * x * star U) * (U * y * star U) = U * (x * y) * star U := by
  calc (U * x * star U) * (U * y * star U)
      = U * x * (star U * U) * y * star U := by simp only [mul_assoc]
    _ = U * x * 1 * y * star U := by rw [hUl]
    _ = U * (x * y) * star U := by
        rw [mul_one]
        simp only [mul_assoc]

/-- Conjugation commutes with the adjoint. -/
theorem conj_star (x : StarStrong.BoundedStarSequence A) :
    star (U * x * star U) = U * star x * star U := by
  rw [star_mul, star_mul, star_star]
  simp only [mul_assoc]

/-- Conjugation is homogeneous. -/
theorem conj_smul (z : ℂ) (x : StarStrong.BoundedStarSequence A) :
    z • (U * x * star U) = U * (z • x) * star U := by
  rw [mul_smul_comm, smul_mul_assoc]

end StarStrongAsymptoticLift

end Conjugate

end

end ShulmanFill
end GroupApproximation
