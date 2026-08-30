import GroupApproximation.Analysis.VoiculescuGlimmPositive

/-!
# (V2) Reducing a general finite set to self-adjoint elements

`GlimmLemmaStatement` asks for approximation on an arbitrary finite subset of
`A`, while the separation argument runs on self-adjoint families — every tuple
of values has to be real for the separating functional to reassemble into a
self-adjoint operator, which is what the connector consumes.

The reduction is the Cartesian decomposition `a = p + i q` with

    `p = 2⁻¹ (a + a⋆)` ,   `q = (2i)⁻¹ (a - a⋆)` ,

both self-adjoint and both in `A`, since `A` is a `⋆`-subalgebra.  Approximating
on `p` and `q` to `ε/2` approximates on `a` to `ε`, because the vector state and
`φ` are both linear and `‖i‖ = 1`.  So a finite set of size `n` becomes a
self-adjoint family of size `2n` and the tolerance halves — which is the whole
of the cost.

Everything is stated inside `↥A` rather than in `B(H)`, because `φ` only eats
elements of `↥A`; the operator-level consequences come from applying the
coercion to the identity, which is one `simp` rather than a chain of
`coe_add`/`coe_smul`/`coe_star` lemmas.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Cartesian decomposition inside a `⋆`-subalgebra.**  Both parts are
self-adjoint and both stay in `A`. -/
theorem exists_selfAdjoint_decomposition {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (a : ↥A) :
    ∃ p q : ↥A, IsSelfAdjoint p ∧ IsSelfAdjoint q ∧
      a = p + Complex.I • q := by
  refine ⟨(2⁻¹ : ℂ) • (a + star a), ((2 * Complex.I)⁻¹ : ℂ) • (a - star a), ?_, ?_, ?_⟩
  · show star _ = _
    rw [star_smul, star_add, star_star, Complex.star_def, map_inv₀,
      Complex.conj_ofNat, add_comm]
  · show star _ = _
    rw [star_smul, star_sub, star_star, Complex.star_def, map_inv₀, map_mul,
      Complex.conj_ofNat, Complex.conj_I, ← neg_sub (star a) a]
    rw [show (2 : ℂ) * -Complex.I = -(2 * Complex.I) by ring, inv_neg, neg_smul,
      smul_neg]
  · have hI : Complex.I * ((2 * Complex.I)⁻¹ : ℂ) = (2⁻¹ : ℂ) := by
      field_simp
    rw [smul_smul, hI, ← smul_add]
    have hsum : a + star a + (a - star a) = (2 : ℂ) • a := by
      rw [two_smul]
      abel
    rw [hsum, smul_smul]
    norm_num

/-- **The reduction.**  Approximating on the two self-adjoint parts to `ε/2`
approximates on the element to `ε`. -/
theorem norm_sub_lt_of_selfAdjoint_parts {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (φ : ↥A →ₚ[ℂ] ℂ) (ξ : H) {a p q : ↥A} {ε : ℝ}
    (hdec : a = p + Complex.I • q)
    (hp : ‖⟪ξ, (p : H →L[ℂ] H) ξ⟫_ℂ - φ p‖ < ε / 2)
    (hq : ‖⟪ξ, (q : H →L[ℂ] H) ξ⟫_ℂ - φ q‖ < ε / 2) :
    ‖⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ - φ a‖ < ε := by
  have hcoe : (a : H →L[ℂ] H) = (p : H →L[ℂ] H) + Complex.I • (q : H →L[ℂ] H) := by
    rw [hdec]
    simp
  have hsplit : ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ - φ a
      = (⟪ξ, (p : H →L[ℂ] H) ξ⟫_ℂ - φ p)
        + Complex.I * (⟪ξ, (q : H →L[ℂ] H) ξ⟫_ℂ - φ q) := by
    rw [hcoe, hdec, map_add, map_smul, smul_eq_mul, add_apply, smul_apply,
      inner_add_right, inner_smul_right]
    ring
  rw [hsplit]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  have hI : ‖Complex.I * (⟪ξ, (q : H →L[ℂ] H) ξ⟫_ℂ - φ q)‖
      = ‖⟪ξ, (q : H →L[ℂ] H) ξ⟫_ℂ - φ q‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hI]
  linarith

end

end ShulmanFill
end GroupApproximation
