import GroupApproximation.Analysis.RationalHermitian

/-!
# The complex numbers with rational real and imaginary parts

The arithmetical route to MF recognition wants its microstates to be *exactly*
unitary and *finitely describable*.  `RationalHermitian.exists_rat_cayley_close`
supplies unitaries of the form `cayley (ofRat Q)` with `Q` rational, which
settles the density half.  What is still needed is that such a matrix is itself
rational, so that it can be written down as finite data --- and that is a
statement about the field, not about matrices: the Cayley transform is built
from ring operations and one inverse, so it suffices that the rational complex
numbers are closed under all of them.

This file records that closure, as a `Subfield ℂ`.  The characterisation used
throughout is by real and imaginary part, which makes every closure proof a
rational-function computation rather than an algebraic manipulation.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace RatComplexSubfield

open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- The complex numbers whose real and imaginary parts are rational. -/
def IsRat (z : ℂ) : Prop := (∃ a : ℚ, z.re = (a : ℝ)) ∧ (∃ b : ℚ, z.im = (b : ℝ))

theorem isRat_zero : IsRat 0 := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

theorem isRat_one : IsRat 1 := ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩

theorem isRat_I : IsRat Complex.I := ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩

theorem isRat_add {z w : ℂ} (hz : IsRat z) (hw : IsRat w) : IsRat (z + w) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hw
  refine ⟨⟨a + c, ?_⟩, ⟨b + d, ?_⟩⟩
  · rw [Complex.add_re, ha, hc]; push_cast; ring
  · rw [Complex.add_im, hb, hd]; push_cast; ring

theorem isRat_neg {z : ℂ} (hz : IsRat z) : IsRat (-z) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  refine ⟨⟨-a, ?_⟩, ⟨-b, ?_⟩⟩
  · rw [Complex.neg_re, ha]; push_cast; ring
  · rw [Complex.neg_im, hb]; push_cast; ring

theorem isRat_mul {z w : ℂ} (hz : IsRat z) (hw : IsRat w) : IsRat (z * w) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hw
  refine ⟨⟨a * c - b * d, ?_⟩, ⟨a * d + b * c, ?_⟩⟩
  · rw [Complex.mul_re, ha, hb, hc, hd]; push_cast; ring
  · rw [Complex.mul_im, ha, hb, hc, hd]; push_cast; ring

theorem isRat_inv {z : ℂ} (hz : IsRat z) : IsRat z⁻¹ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  rcases eq_or_ne z 0 with hzero | hzero
  · rw [hzero, inv_zero]; exact isRat_zero
  have hnorm : Complex.normSq z = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rw [Complex.normSq_apply, ha, hb]; ring
  have hne : Complex.normSq z ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hzero
  have hden : ((a : ℚ) ^ 2 + (b : ℚ) ^ 2 : ℚ) ≠ 0 := by
    intro hcon
    apply hne
    rw [hnorm]
    have : ((a : ℚ) ^ 2 + (b : ℚ) ^ 2 : ℚ) = 0 := hcon
    have hcast : ((((a : ℚ) ^ 2 + (b : ℚ) ^ 2 : ℚ) : ℝ)) = 0 := by
      rw [this]; norm_num
    push_cast at hcast
    linarith
  refine ⟨⟨a / (a ^ 2 + b ^ 2), ?_⟩, ⟨-b / (a ^ 2 + b ^ 2), ?_⟩⟩
  · rw [Complex.inv_re, ha, hnorm]
    push_cast
    field_simp
  · rw [Complex.inv_im, hb, hnorm]
    push_cast
    field_simp

/-- **The rational complex numbers form a subfield.** -/
def ratSubfield : Subfield ℂ where
  carrier := {z | IsRat z}
  mul_mem' := isRat_mul
  one_mem' := isRat_one
  add_mem' := isRat_add
  zero_mem' := isRat_zero
  neg_mem' := isRat_neg
  inv_mem' := fun _ hz => isRat_inv hz

@[simp] theorem mem_ratSubfield {z : ℂ} : z ∈ ratSubfield ↔ IsRat z := Iff.rfl

/-! ## Relation to the explicit rational form -/

theorem isRat_ofRatPair (q : ℚ × ℚ) :
    IsRat (RationalHermitian.ofRatPair q) :=
  ⟨⟨q.1, by simp⟩, ⟨q.2, by simp⟩⟩

theorem exists_ofRatPair_of_isRat {z : ℂ} (hz : IsRat z) :
    ∃ q : ℚ × ℚ, z = RationalHermitian.ofRatPair q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  refine ⟨(a, b), ?_⟩
  apply Complex.ext
  · rw [ha]; simp
  · rw [hb]; simp

/-! ## Matrices with rational entries

Determinant, adjugate and inverse are built from ring operations and one field
inverse, so each stays inside the subfield.  The Cayley transform is then
rational as well, which is what lets a microstate be written down as finite
data. -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_isRat {M : Matrix n n ℂ} (h : ∀ i j, IsRat (M i j)) :
    IsRat M.det := by
  rw [Matrix.det_apply]
  refine Subfield.sum_mem ratSubfield fun σ _ => ?_
  refine zsmul_mem ?_ _
  exact Subfield.prod_mem ratSubfield fun i _ => h (σ i) i

theorem adjugate_isRat {M : Matrix n n ℂ} (h : ∀ i j, IsRat (M i j)) (i j : n) :
    IsRat (M.adjugate i j) := by
  rw [Matrix.adjugate_apply]
  refine det_isRat ?_
  intro k l
  rw [Matrix.updateRow_apply]
  by_cases hk : k = j
  · rw [if_pos hk]
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]; exact isRat_one
    · rw [Pi.single_eq_of_ne hl]; exact isRat_zero
  · rw [if_neg hk]; exact h k l

theorem inv_isRat {M : Matrix n n ℂ} (h : ∀ i j, IsRat (M i j)) (i j : n) :
    IsRat (M⁻¹ i j) := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine isRat_mul ?_ (adjugate_isRat h i j)
  rw [Ring.inverse_eq_inv']
  exact isRat_inv (det_isRat h)

omit [Fintype n] in
theorem one_isRat (i j : n) : IsRat ((1 : Matrix n n ℂ) i j) := by
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij]; exact isRat_one
  · rw [if_neg hij]; exact isRat_zero

omit [Fintype n] in
theorem denom_isRat {H : Matrix n n ℂ} (h : ∀ i j, IsRat (H i j)) (i j : n) :
    IsRat (CayleyUnitary.denom H i j) := by
  rw [CayleyUnitary.denom, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact isRat_add (one_isRat i j) (isRat_mul isRat_I (h i j))

/-- **The Cayley transform of a rational matrix is rational.** -/
theorem cayley_isRat {H : Matrix n n ℂ} (h : ∀ i j, IsRat (H i j)) (i j : n) :
    IsRat (CayleyUnitary.cayley H i j) := by
  rw [CayleyUnitary.cayley, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine isRat_add ?_ (isRat_neg (one_isRat i j))
  · refine isRat_mul ?_ (inv_isRat (denom_isRat h) i j)
    exact ⟨⟨2, by norm_num⟩, ⟨0, by norm_num⟩⟩

/-- **The Cayley transform of rational data is again rational data.** -/
theorem exists_rat_cayley (Q : Matrix n n (ℚ × ℚ)) :
    ∃ Q' : Matrix n n (ℚ × ℚ),
      CayleyUnitary.cayley (RationalHermitian.ofRat Q)
        = RationalHermitian.ofRat Q' := by
  classical
  have hQ : ∀ i j, IsRat (RationalHermitian.ofRat Q i j) := fun i j =>
    isRat_ofRatPair (Q i j)
  have hchoice : ∀ i j : n, ∃ q : ℚ × ℚ,
      CayleyUnitary.cayley (RationalHermitian.ofRat Q) i j
        = RationalHermitian.ofRatPair q := fun i j =>
    exists_ofRatPair_of_isRat (cayley_isRat hQ i j)
  choose Q' hQ' using hchoice
  exact ⟨Q', by ext i j; exact hQ' i j⟩

end Matrices

/-! ## The density statement, with rational data -/

/-- **The rational unitaries are dense in the unitary group.**

Every unitary is approximated by a matrix that is *exactly* unitary and whose
entries all have rational real and imaginary parts.  This is the statement the
arithmetical route needs: the approximating matrices range over a countable set
carrying an explicit encoding, and each one is a genuine unitary rather than an
approximate one, so a microstate built from them is a microstate on the nose.

The three inputs are density of the Cayley image
(`UnitaryPerturbation.exists_hermitian_cayley_close`), density of the rational
Hermitian parameters (`RationalHermitian.exists_rat_hermitian_close`) against
the Lipschitz bound (`CayleyUnitary.norm_cayley_sub_cayley`), and rationality of
the transform itself (`exists_rat_cayley`). -/
theorem exists_rat_unitary_close {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Matrix n n (ℚ × ℚ),
      RationalHermitian.ofRat Q ∈ Matrix.unitaryGroup n ℂ ∧
      ‖U - RationalHermitian.ofRat Q‖ < ε := by
  obtain ⟨Q₀, hQ₀herm, hQ₀close⟩ :=
    RationalHermitian.exists_rat_cayley_close hU hε
  obtain ⟨Q, hQ⟩ := exists_rat_cayley Q₀
  refine ⟨Q, ?_, ?_⟩
  · rw [← hQ]
    exact CayleyUnitary.cayley_mem_unitaryGroup hQ₀herm
  · rw [← hQ]
    exact hQ₀close

end RatComplexSubfield
end GroupApproximation
