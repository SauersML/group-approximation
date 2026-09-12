import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Hilbert--Schmidt control does not transfer to the adjoint operators

The limitations section opens with a negative claim: *if multiplication is
controlled only in normalized Hilbert--Schmidt norm, the induced adjoint
operators on the Hilbert--Schmidt spaces need not be close in operator norm.*
This file makes that claim machine-checked, and makes it exactly sharp against
the positive theorem it is contrasted with.

`AdjointMatrix.l2_opNorm_conjDouble_sub_le_two` is the positive half already in
the repository: for unitary `U, V`,

`‖Ad(U) - Ad(V)‖ ≤ 2 ‖U - V‖`

in *operator* norm, with no dimension loss.  The theorem below is the exact
failure of the same estimate when `‖U - V‖` is replaced by the normalized
Hilbert--Schmidt distance: the left-hand side stays at its maximum `2` while
the right-hand side goes to zero.

## The witness

The witness is the cheapest one available, and it is dimension-driven rather
than exotic: `U = 1` and `V` the sign diagonal flipping a single coordinate
`i₀`.  Then

* `U - V` has one nonzero entry, of modulus `2`, so its Frobenius mass is `4`
  in every dimension and its normalized Hilbert--Schmidt distance is `2/√d`;
* but `Ad(V)` negates every off-diagonal matrix unit in the `i₀`-row --- on
  `X = e_{i₀ i₁}` with `i₁ ≠ i₀` one has `V X V⋆ = -X` --- so
  `(Ad(U) - Ad(V))(X) = 2X` and the operator norm is at least `2`,
  independently of `d`.

So the two norms disagree by an unbounded factor, and the disagreement is not
a defect of the constant `2`: `2` is simultaneously the sharp upper bound in
operator norm and a lower bound here.  This is why both transport proofs need
operator-norm multiplicativity, and why a Hilbert--Schmidt hypothesis alone
supplies nothing --- the companion statement to `NormModel.exists_hs_collapse`,
which collapses Hilbert--Schmidt distances by padding while leaving every
operator-norm quantity fixed.
-/

namespace GroupApproximation
namespace HilbertSchmidtAdjointGap

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

section General

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The sign diagonal and the matrix unit -/

/-- The diagonal unitary that flips exactly the coordinate `i₀`. -/
def signDiagonal (i₀ : Y) : Matrix Y Y ℂ :=
  Matrix.diagonal fun i ↦ if i = i₀ then -1 else 1

omit [Fintype Y] in
theorem signDiagonal_apply (i₀ i j : Y) :
    signDiagonal i₀ i j =
      if i = j then (if i = i₀ then (-1 : ℂ) else 1) else 0 := by
  simp only [signDiagonal, Matrix.diagonal_apply]

theorem signDiagonal_mem_unitaryGroup (i₀ : Y) :
    signDiagonal i₀ ∈ Matrix.unitaryGroup Y ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [signDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply]
  by_cases hi : i = i₀ <;> simp [hi]

/-- The matrix unit at `(i₀, i₁)`, written out rather than imported so that no
naming convention for standard basis matrices is relied on. -/
def unitMatrix (i₀ i₁ : Y) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ if i = i₀ ∧ j = i₁ then 1 else 0

omit [Fintype Y] in
@[simp] theorem unitMatrix_apply (i₀ i₁ i j : Y) :
    unitMatrix i₀ i₁ i j = if i = i₀ ∧ j = i₁ then 1 else 0 := rfl

/-- The matrix unit carries unit Frobenius mass. -/
theorem sum_normSq_unitMatrix (i₀ i₁ : Y) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (unitMatrix i₀ i₁ i j) = 1 := by
  classical
  have hrow : ∀ i : Y, ∑ j : Y, Complex.normSq (unitMatrix i₀ i₁ i j) =
      if i = i₀ then (1 : ℝ) else 0 := by
    intro i
    by_cases hi : i = i₀
    · rw [if_pos hi, Finset.sum_eq_single i₁]
      · simp [unitMatrix_apply, hi]
      · intro j _ hj
        simp [unitMatrix_apply, hj]
      · intro hmem
        exact absurd (Finset.mem_univ i₁) hmem
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp [unitMatrix_apply, hi]
  have hsum : ∑ i : Y, ∑ j : Y, Complex.normSq (unitMatrix i₀ i₁ i j) =
      ∑ i : Y, (if i = i₀ then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun i _ ↦ hrow i
  rw [hsum, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [hi]
  · intro hmem
    exact absurd (Finset.mem_univ i₀) hmem

/-! ## The Hilbert--Schmidt side: the two unitaries are close -/

omit [Fintype Y] in
/-- The difference `1 - V` has a single nonzero entry, of modulus `2`. -/
theorem one_sub_signDiagonal_apply (i₀ i j : Y) :
    ((1 : Matrix Y Y ℂ) - signDiagonal i₀) i j =
      if i = j then (if i = i₀ then (2 : ℂ) else 0) else 0 := by
  classical
  rw [Matrix.sub_apply, Matrix.one_apply, signDiagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = i₀
    · norm_num [hi]
    · simp [hi]
  · simp [hij]

omit [Fintype Y] in
/-- On the diagonal, `1 - V` is `2` at `i₀` and `0` elsewhere. -/
theorem one_sub_signDiagonal_diag (i₀ i : Y) :
    ((1 : Matrix Y Y ℂ) - signDiagonal i₀) i i =
      if i = i₀ then (2 : ℂ) else 0 := by
  rw [one_sub_signDiagonal_apply, if_pos rfl]

/-- Complex modulus squared of the single nonzero entry. -/
theorem normSq_two : Complex.normSq (2 : ℂ) = 4 := by
  rw [Complex.normSq_apply]
  norm_num

/-- The Frobenius mass of `1 - V` is `4`, in every dimension. -/
theorem sum_normSq_one_sub_signDiagonal (i₀ : Y) :
    ∑ i : Y, ∑ j : Y,
      Complex.normSq (((1 : Matrix Y Y ℂ) - signDiagonal i₀) i j) = 4 := by
  classical
  have hrow : ∀ i : Y, ∑ j : Y,
      Complex.normSq (((1 : Matrix Y Y ℂ) - signDiagonal i₀) i j) =
      if i = i₀ then (4 : ℝ) else 0 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [one_sub_signDiagonal_diag]
      by_cases hi : i = i₀
      · rw [if_pos hi, if_pos hi]
        exact normSq_two
      · rw [if_neg hi, if_neg hi]
        exact Complex.normSq_zero
    · intro j _ hj
      rw [one_sub_signDiagonal_apply, if_neg (Ne.symm hj)]
      exact Complex.normSq_zero
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  have hsum : ∑ i : Y, ∑ j : Y,
      Complex.normSq (((1 : Matrix Y Y ℂ) - signDiagonal i₀) i j) =
      ∑ i : Y, (if i = i₀ then (4 : ℝ) else 0) :=
    Finset.sum_congr rfl fun i _ ↦ hrow i
  rw [hsum, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [hi]
  · intro hmem
    exact absurd (Finset.mem_univ i₀) hmem

/-! ## The operator side: the adjoints stay far apart -/

/-- Conjugating the matrix unit `e_{i₀ i₁}` by the sign diagonal negates it,
because exactly one of the two indices is flipped. -/
theorem signDiagonal_conj_unitMatrix {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    signDiagonal i₀ * unitMatrix i₀ i₁ * (signDiagonal i₀)ᴴ =
      -unitMatrix i₀ i₁ := by
  classical
  ext a b
  simp only [signDiagonal, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.neg_apply, Pi.star_apply, unitMatrix_apply]
  by_cases ha : a = i₀ <;> by_cases hb : b = i₁ <;>
    simp [ha, hb, Ne.symm h]

/-- **The adjoint operators stay far apart.**  Whenever the coordinate type
carries two distinct points, the conjugation operators of `1` and of the sign
diagonal differ by at least `2` in operator norm on the Hilbert--Schmidt
space --- with no dependence on the dimension. -/
theorem two_le_l2_opNorm_conjDouble_sub {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    (2 : ℝ) ≤
      ‖conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀)‖ := by
  classical
  have hone : conjDouble (1 : Matrix Y Y ℂ) *ᵥ rowVec (unitMatrix i₀ i₁) =
      rowVec (unitMatrix i₀ i₁) := by
    rw [conjDouble_mulVec_rowVec]
    simp
  have hsign : conjDouble (signDiagonal i₀) *ᵥ rowVec (unitMatrix i₀ i₁) =
      rowVec (-unitMatrix i₀ i₁) := by
    rw [conjDouble_mulVec_rowVec, signDiagonal_conj_unitMatrix h]
  have hdiff : (conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀)) *ᵥ
      rowVec (unitMatrix i₀ i₁) = rowVec ((2 : ℂ) • unitMatrix i₀ i₁) := by
    rw [Matrix.sub_mulVec, hone, hsign]
    funext p
    simp only [rowVec, Pi.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  have hpt : ∀ p : Y × Y,
      Complex.normSq (rowVec ((2 : ℂ) • unitMatrix i₀ i₁) p) =
        4 * Complex.normSq (rowVec (unitMatrix i₀ i₁) p) := by
    intro p
    simp only [rowVec, Matrix.smul_apply, smul_eq_mul]
    rw [Complex.normSq_mul, normSq_two]
  have hmassRight : ∑ p : Y × Y,
      Complex.normSq (rowVec (unitMatrix i₀ i₁) p) = 1 := by
    rw [sum_normSq_rowVec, sum_normSq_unitMatrix]
  have hmassLeft : ∑ p : Y × Y, Complex.normSq
      (((conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀)) *ᵥ
        rowVec (unitMatrix i₀ i₁)) p) = 4 := by
    have hstep : ∑ p : Y × Y, Complex.normSq
        (((conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀)) *ᵥ
          rowVec (unitMatrix i₀ i₁)) p) =
        ∑ p : Y × Y, 4 * Complex.normSq (rowVec (unitMatrix i₀ i₁) p) := by
      rw [hdiff]
      exact Finset.sum_congr rfl fun p _ ↦ hpt p
    rw [hstep, ← Finset.mul_sum, hmassRight, mul_one]
  have hbound := sum_normSq_mulVec_le_general
    (conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀))
    (rowVec (unitMatrix i₀ i₁))
  rw [hmassLeft, hmassRight, mul_one] at hbound
  nlinarith [norm_nonneg
    (conjDouble (1 : Matrix Y Y ℂ) - conjDouble (signDiagonal i₀))]

end General

/-! ## The manuscript's statement -/

/-- The normalized Hilbert--Schmidt distance between `1` and the sign diagonal
is `4 / d`: the Frobenius mass is fixed while the normalization grows. -/
theorem hsNormSq_one_sub_signDiagonal (Y : FiniteModel) (i₀ : Y) :
    hsNormSq Y ((1 : Matrix Y Y ℂ) - signDiagonal i₀) =
      4 / (Fintype.card Y : ℝ) := by
  simp only [hsNormSq]
  rw [sum_normSq_one_sub_signDiagonal]

/-- **Hilbert--Schmidt control does not transfer to the adjoints.**  For every
tolerance there are a finite model and two unitaries whose normalized
Hilbert--Schmidt distance is below that tolerance, while their conjugation
operators on the Hilbert--Schmidt space differ by at least `2` in operator
norm.

Read against `AdjointMatrix.l2_opNorm_conjDouble_sub_le_two`, which bounds the
same left-hand side by `2 ‖U - V‖` in operator norm, this is the exact
statement that the operator-norm hypothesis of both transport proofs cannot be
weakened to a Hilbert--Schmidt hypothesis. -/
theorem exists_hsClose_adjointFar :
    ∀ ε : ℝ, 0 < ε → ∃ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
      U ∈ Matrix.unitaryGroup Y ℂ ∧ V ∈ Matrix.unitaryGroup Y ℂ ∧
      Real.sqrt (hsNormSq Y (U - V)) ≤ ε ∧
      2 ≤ ‖conjDouble U - conjDouble V‖ := by
  intro ε hε
  obtain ⟨d, hd⟩ := exists_nat_gt (4 / ε ^ 2)
  have hzero : (0 : ℕ) < d + 2 := by omega
  have hone : (1 : ℕ) < d + 2 := by omega
  refine ⟨naturalFiniteModel (d + 2), 1,
    signDiagonal (⟨0, hzero⟩ : Fin (d + 2)), Submonoid.one_mem _,
    signDiagonal_mem_unitaryGroup _, ?_, ?_⟩
  · have hcard :
        (Fintype.card (naturalFiniteModel (d + 2)) : ℝ) = (d : ℝ) + 2 := by
      simp
    have hpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
    have hlt : 4 / ε ^ 2 < (d : ℝ) + 2 := by
      have hdd : (4 : ℝ) / ε ^ 2 < (d : ℝ) := hd
      linarith
    rw [div_lt_iff₀ hεsq] at hlt
    have hle : hsNormSq (naturalFiniteModel (d + 2))
        ((1 : Matrix (naturalFiniteModel (d + 2))
          (naturalFiniteModel (d + 2)) ℂ) -
            signDiagonal (⟨0, hzero⟩ : Fin (d + 2))) ≤ ε ^ 2 := by
      rw [hsNormSq_one_sub_signDiagonal, hcard, div_le_iff₀ hpos]
      nlinarith
    calc
      Real.sqrt (hsNormSq (naturalFiniteModel (d + 2))
          ((1 : Matrix (naturalFiniteModel (d + 2))
            (naturalFiniteModel (d + 2)) ℂ) -
              signDiagonal (⟨0, hzero⟩ : Fin (d + 2))))
          ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
      _ = ε := Real.sqrt_sq hε.le
  · have hne : (⟨0, hzero⟩ : Fin (d + 2)) ≠ (⟨1, hone⟩ : Fin (d + 2)) := by
      simp
    exact two_le_l2_opNorm_conjDouble_sub
      (i₁ := (⟨1, hone⟩ : Fin (d + 2))) hne

/-- **No vanishing modulus controls the adjoint defect from Hilbert--Schmidt
closeness.**  There is no function `m` with `m δ → 0` as `δ → 0⁺` such that
every pair of unitaries of every finite model satisfies
`‖conjDouble U - conjDouble V‖ ≤ m δ` whenever its normalized
Hilbert--Schmidt distance is at most `δ`: by `exists_hsClose_adjointFar` the
adjoint defect stays at `2` at every tolerance, while a vanishing modulus is
eventually below `2`.

This is the manuscript's sentence about the *method*, not only about a pair
of witnesses: the adjoint spectral estimates require operator-norm
multiplicative control, and no estimate through the normalized
Hilbert--Schmidt distance alone -- however weak its modulus -- can supply
it. -/
theorem no_vanishing_modulus_controls_adjoint :
    ¬ ∃ m : ℝ → ℝ,
      Filter.Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
        U ∈ Matrix.unitaryGroup Y ℂ → V ∈ Matrix.unitaryGroup Y ℂ →
        ∀ δ : ℝ, 0 < δ → Real.sqrt (hsNormSq Y (U - V)) ≤ δ →
          ‖conjDouble U - conjDouble V‖ ≤ m δ := by
  rintro ⟨m, hm, hcontrol⟩
  have hIio : ∀ᶠ s in nhds (0 : ℝ), s < 2 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with s hs
    exact hs
  have h2 : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), m δ < 2 := hm.eventually hIio
  obtain ⟨δ, hδ2, hδmem⟩ :=
    (h2.and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := Set.mem_Ioi.mp hδmem
  obtain ⟨Y, U, V, hU, hV, hdist, hfar⟩ := exists_hsClose_adjointFar δ hδpos
  have := hcontrol Y U V hU hV δ hδpos hdist
  linarith

end

end HilbertSchmidtAdjointGap
end GroupApproximation
