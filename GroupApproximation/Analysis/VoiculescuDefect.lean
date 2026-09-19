import GroupApproximation.Analysis.VoiculescuSequentialUnit

/-!
# (V1b) The commutator defects of a sequential unit, and why they almost annihilate

`Analysis/VoiculescuSequentialUnit` produced a sequence of compact self-adjoint
contractions absorbing every compact operator from both sides.  Its members do
*not* almost commute with a given bounded `S`: the defects
`eₙ S - S eₙ` converge to `0` strongly and, in general, not in norm — that is
exactly why the quasicentral statement is a theorem and not a triviality.

What is true, and is what `Analysis/VoiculescuAlmostOrthogonal` will spend, is
that the defects at *widely separated* indices are almost orthogonal.  The
computation is three lines and uses only the right-handed absorption:

    Dq ⬝ (eₙ S - S eₙ)⋆ = Dq (S⋆ eₙ - eₙ S⋆)
                       = (Dq S⋆) eₙ - (Dq eₙ) S⋆
                       = ((Dq S⋆) eₙ - Dq S⋆) - ((Dq eₙ) - Dq) S⋆ ,

whose two brackets are `‖K eₙ - K‖` for the compact operators `K = Dq S⋆` and
`K = Dq`, and those tend to `0` because the unit absorbs compacts.  So for each
fixed `q` the products `Dq Dₙ⋆` tend to `0` in norm as `n → ∞`, which is the
input the almost-orthogonality estimate asks for.

The self-adjointness of the members is used once, to move the star across `eₙ`;
without it the second bracket would be `‖K eₙ⋆ - K‖`, which the structure does
not bound.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The commutator defect** of the `n`-th member of a sequential unit against
a bounded operator `S`.  Quasicentrality is the assertion that these tend to
`0` in norm along a suitable sequence. -/
def quasicentralDefect (u : SequentialCompactUnit H) (S : H →L[ℂ] H) (n : ℕ) :
    H →L[ℂ] H :=
  u.toFun n * S - S * u.toFun n

theorem quasicentralDefect_eq (u : SequentialCompactUnit H) (S : H →L[ℂ] H) (n : ℕ) :
    quasicentralDefect u S n = u.toFun n * S - S * u.toFun n := rfl

/-- Each defect is compact: the ideal of compacts absorbs `S` on either side. -/
theorem isCompactOperator_quasicentralDefect (u : SequentialCompactUnit H)
    (S : H →L[ℂ] H) (n : ℕ) : IsCompactOperator (quasicentralDefect u S n) :=
  ((u.isCompact n).comp_clm S).sub ((u.isCompact n).clm_comp S)

/-- Each defect is bounded by twice the norm of `S`, since the members are
contractions.  This is the `M` of the almost-orthogonality estimate. -/
theorem norm_quasicentralDefect_le (u : SequentialCompactUnit H) (S : H →L[ℂ] H)
    (n : ℕ) : ‖quasicentralDefect u S n‖ ≤ 2 * ‖S‖ := by
  have h1 : ‖u.toFun n * S‖ ≤ ‖S‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg S) (u.norm_le n))
  have h2 : ‖S * u.toFun n‖ ≤ ‖S‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg S) (u.norm_le n))
  rw [quasicentralDefect_eq]
  calc ‖u.toFun n * S - S * u.toFun n‖ ≤ ‖u.toFun n * S‖ + ‖S * u.toFun n‖ :=
        norm_sub_le _ _
    _ ≤ 2 * ‖S‖ := by linarith

/-- The adjoint of a defect is the defect against `S⋆`, up to sign; the members
are self-adjoint, so the star only moves `S`. -/
theorem star_quasicentralDefect (u : SequentialCompactUnit H) (S : H →L[ℂ] H)
    (n : ℕ) : star (quasicentralDefect u S n)
      = star S * u.toFun n - u.toFun n * star S := by
  rw [quasicentralDefect_eq, star_sub, star_mul, star_mul, (u.isSelfAdjoint n).star_eq]

/-- **The identity behind the almost orthogonality.**  The product of a fixed
defect with the adjoint of a later one is a difference of two absorption
errors, so it is small as soon as the later index is large. -/
theorem quasicentralDefect_mul_star (u : SequentialCompactUnit H) (S : H →L[ℂ] H)
    (q n : ℕ) : quasicentralDefect u S q * star (quasicentralDefect u S n)
      = (quasicentralDefect u S q * star S * u.toFun n - quasicentralDefect u S q * star S)
        - (quasicentralDefect u S q * u.toFun n - quasicentralDefect u S q) * star S := by
  rw [star_quasicentralDefect]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- The two absorption errors bound the product.  Kept apart from the limit so
that the limit's proof never has to rewrite inside a `star`. -/
theorem norm_quasicentralDefect_mul_star_le (u : SequentialCompactUnit H)
    (S : H →L[ℂ] H) (q n : ℕ) :
    ‖quasicentralDefect u S q * star (quasicentralDefect u S n)‖
      ≤ ‖quasicentralDefect u S q * star S * u.toFun n
          - quasicentralDefect u S q * star S‖
        + ‖quasicentralDefect u S q * u.toFun n - quasicentralDefect u S q‖ * ‖S‖ := by
  rw [quasicentralDefect_mul_star]
  refine (norm_sub_le _ _).trans ?_
  have hmul := norm_mul_le
    (quasicentralDefect u S q * u.toFun n - quasicentralDefect u S q) (star S)
  rw [norm_star] at hmul
  linarith

/-- **The cross terms vanish.**  For a fixed index `q`, the products
`Dq Dₙ⋆` tend to `0` in norm.  Both summands of
`quasicentralDefect_mul_star` are absorption errors of compact operators, and
the unit absorbs compacts on the right. -/
theorem tendsto_norm_quasicentralDefect_mul_star (u : SequentialCompactUnit H)
    (S : H →L[ℂ] H) (q : ℕ) :
    Tendsto (fun n ↦ ‖quasicentralDefect u S q * star (quasicentralDefect u S n)‖)
      atTop (𝓝 0) := by
  have hDc : IsCompactOperator (quasicentralDefect u S q) :=
    isCompactOperator_quasicentralDefect u S q
  have hEc : IsCompactOperator (quasicentralDefect u S q * star S) :=
    hDc.comp_clm (star S)
  have hE0 : Tendsto (fun n ↦ ‖quasicentralDefect u S q * star S * u.toFun n
      - quasicentralDefect u S q * star S‖) atTop (𝓝 0) :=
    Tendsto.congr (fun n ↦ norm_sub_rev _ _)
      (u.tendsto_right (quasicentralDefect u S q * star S) hEc)
  have hD0 : Tendsto (fun n ↦ ‖quasicentralDefect u S q * u.toFun n
      - quasicentralDefect u S q‖) atTop (𝓝 0) :=
    Tendsto.congr (fun n ↦ norm_sub_rev _ _)
      (u.tendsto_right (quasicentralDefect u S q) hDc)
  have hsum : Tendsto (fun n ↦ ‖quasicentralDefect u S q * star S * u.toFun n
      - quasicentralDefect u S q * star S‖
      + ‖quasicentralDefect u S q * u.toFun n - quasicentralDefect u S q‖ * ‖S‖)
      atTop (𝓝 0) := by
    have h := hE0.add (hD0.mul_const ‖S‖)
    simpa using h
  exact squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ norm_quasicentralDefect_mul_star_le u S q n) hsum

end

end ShulmanFill
end GroupApproximation
