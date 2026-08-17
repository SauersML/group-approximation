import GroupApproximation.Sofic.FrobeniusPairing
import GroupApproximation.Sofic.UltrafilterLimit
import GroupApproximation.Sofic.UltraproductModelConstruction

/-!
# The inner product of `K_ω`, on the numerator

`Sofic/UltraproductModelConstruction.lean` builds the underlying module of the
manuscript's `K_ω` — mass-bounded families modulo families null at the weight
along `ω` — and says in its own docstring that the inner product
`⟨[ξ], [η]⟩ = lim_ω Tr(η_n* ξ_n)/w_n` is *deliberately not built*, so that `Vec`
is never called a Hilbert space.  The printed proof of
`thm:kazhdan-transport` uses `K_ω` as a Hilbert space throughout: orthogonal
complements of the fixed subspace, unit vectors moved by a generator, and the
norm of `A[ξ_n]_ω`.  This file supplies the form on the numerator; the quotient
and the `InnerProductSpace` instance follow in
`Sofic/HilbertUltraproductSpace.lean`.

## Why no Cauchy--Schwarz appears

The one estimate that needs care is that a family null at the weight pairs to
zero against every mass-bounded family.  Cauchy--Schwarz gives it at once, but
so does the arithmetic-geometric bound of `Sofic/FrobeniusPairing.lean` applied
after rescaling one argument: for every `t > 0`,

  `‖⟨ζ_n, η_n⟩‖ ≤ t · (mass ζ_n / w_n) / 2 + (mass η_n / w_n) / (2t)`,

so a null `ζ` makes the first term vanish along `ω` and the second is `Cy/(2t)`,
which `t` can make as small as required.  That keeps the whole file elementary
and independent of any completed structure.
-/

namespace GroupApproximation
namespace HilbertUltraproductPairing

open Filter Matrix
open FrobeniusPairing UltrafilterLimit UltraproductModelConstruction
open ScaledKazhdanTransport

noncomputable section

variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ)

/-- **The coordinate inner product of `K_n`**: the Frobenius pairing divided by
the weight, exactly `Tr(ξ_n* η_n)/w_n`. -/
def pairAt (ξ η : MatFam Y) (n : ℕ) : ℂ :=
  (((ξ n)ᴴ * η n).trace) / ((w n : ℝ) : ℂ)

variable {Y w}

/-- A mass-bounded family vanishes at every stage where the weight does. -/
theorem eq_zero_of_weight_eq_zero {C : ℝ} {ξ : MatFam Y}
    (hξ : ∀ n, matMass (ξ n) ≤ C * w n) {n : ℕ} (hn : w n = 0) : ξ n = 0 := by
  have h0 : matMass (ξ n) ≤ 0 := by
    have h := hξ n
    rwa [hn, mul_zero] at h
  exact UltraproductScaledTransport.eq_zero_of_matMass_eq_zero
    (le_antisymm h0 (matMass_nonneg _))

@[simp] theorem pairAt_zero_left (η : MatFam Y) (n : ℕ) :
    pairAt Y w (0 : MatFam Y) η n = 0 := by
  simp [pairAt]

/-- The pairing is additive in the second argument. -/
theorem pairAt_add_right (ξ η ζ : MatFam Y) (n : ℕ) :
    pairAt Y w ξ (fun k ↦ η k + ζ k) n = pairAt Y w ξ η n + pairAt Y w ξ ζ n := by
  rw [pairAt, pairAt, pairAt, ← add_div, Matrix.mul_add, Matrix.trace_add]

/-- The pairing is homogeneous in the second argument. -/
theorem pairAt_smul_right (c : ℂ) (ξ η : MatFam Y) (n : ℕ) :
    pairAt Y w ξ (fun k ↦ c • η k) n = c * pairAt Y w ξ η n := by
  rw [pairAt, pairAt, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    mul_div_assoc]

/-- Conjugate symmetry, stagewise. -/
theorem pairAt_conj (ξ η : MatFam Y) (n : ℕ) :
    (starRingEnd ℂ) (pairAt Y w ξ η n) = pairAt Y w η ξ n := by
  rw [pairAt, pairAt, map_div₀, trace_conjTranspose_mul_comm]
  congr 1
  simp

/-- The self-pairing is the renormalized mass, which is what makes the form
positive. -/
theorem pairAt_self (ξ : MatFam Y) (n : ℕ) :
    pairAt Y w ξ ξ n = ((matMass (ξ n) / w n : ℝ) : ℂ) := by
  rw [pairAt, trace_conjTranspose_mul_self]
  push_cast
  rfl

/-! ## Boundedness -/

/-- **The bound that makes `lim_ω` exist.**  Two mass-bounded families have
uniformly bounded coordinate pairings. -/
theorem norm_pairAt_le (hw : ∀ n, 0 ≤ w n) {ξ η : MatFam Y} {Cx Cy : ℝ}
    (hξ : ∀ n, matMass (ξ n) ≤ Cx * w n) (hη : ∀ n, matMass (η n) ≤ Cy * w n)
    (n : ℕ) : ‖pairAt Y w ξ η n‖ ≤ (max Cx 0 + max Cy 0) / 2 := by
  rcases (hw n).lt_or_eq with hpos | hzero
  · have hbound := norm_trace_conjTranspose_mul_le (ξ n) (η n)
    have hx := hξ n
    have hy := hη n
    have hxle : Cx ≤ max Cx 0 := le_max_left _ _
    have hyle : Cy ≤ max Cy 0 := le_max_left _ _
    rw [pairAt, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith [hbound, hx, hy, hpos.le, matMass_nonneg (ξ n),
      matMass_nonneg (η n)]
  · have hxn : ξ n = 0 := eq_zero_of_weight_eq_zero hξ hzero.symm
    have hz : pairAt Y w ξ η n = 0 := by simp [pairAt, hxn]
    rw [hz, norm_zero]
    have h1 : (0 : ℝ) ≤ max Cx 0 := le_max_right _ _
    have h2 : (0 : ℝ) ≤ max Cy 0 := le_max_right _ _
    linarith

/-- The rescaled form of the same bound, which is the substitute for
Cauchy--Schwarz used at the null step. -/
theorem norm_pairAt_le_scaled (hw : ∀ n, 0 ≤ w n) {t : ℝ} (ht : 0 < t)
    (ξ η : MatFam Y) (n : ℕ) :
    ‖pairAt Y w ξ η n‖
      ≤ t * (matMass (ξ n) / w n) / 2 + (matMass (η n) / w n) / (2 * t) := by
  rcases (hw n).lt_or_eq with hpos | hzero
  · have hbound :=
      norm_trace_conjTranspose_mul_le (((t : ℝ) : ℂ) • ξ n) (η n)
    have hmass : matMass (((t : ℝ) : ℂ) • ξ n) = t ^ 2 * matMass (ξ n) := by
      rw [matMass_smul]
      simp [Complex.normSq_ofReal, sq]
    have htr : (((((t : ℝ) : ℂ) • ξ n)ᴴ * η n).trace)
        = ((t : ℝ) : ℂ) * (((ξ n)ᴴ * η n).trace) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul]
      congr 1
      simp
    rw [hmass, htr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at hbound
    rw [pairAt, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    rw [div_le_iff₀ hpos]
    have hwne : w n ≠ 0 := ne_of_gt hpos
    field_simp
    nlinarith [hbound, ht, hpos, matMass_nonneg (ξ n), matMass_nonneg (η n),
      norm_nonneg (((ξ n)ᴴ * η n).trace)]
  · have hz : pairAt Y w ξ η n = 0 := by
      simp [pairAt, ← hzero]
    rw [hz, norm_zero, ← hzero]
    simp

end

end HilbertUltraproductPairing
end GroupApproximation
