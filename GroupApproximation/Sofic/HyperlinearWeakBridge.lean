import GroupApproximation.Sofic.HyperlinearNonScalar
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.HyperlinearScalar
import GroupApproximation.Sofic.NormTraceGap

/-!
# From fixed tracial separation to hyperlinearity

A homomorphism into a tracial matrix ultraproduct initially supplies only a
fixed positive Hilbert--Schmidt separation.  This file gives an elementary
bridge from that fixed separation to the near-maximal separation used by
`IsHyperlinear`.

The key device is the unital padding `U ↦ U ⊕ 1` with an identity block of
the same dimension.  If `z` is the relative normalized trace of two original
unitaries, their padded relative trace is `(z + 1) / 2`.  Positive squared
Hilbert--Schmidt separation bounds `re z` away from `1`; the padding therefore
bounds `|(z + 1) / 2|` away from `1`, including when `z` is a scalar phase.
The conjugate-double amplification already formalized in
`HyperlinearNonScalar` then gives full hyperlinearity.
-/

namespace GroupApproximation

open Matrix

variable {G : Type*} [Group G]

/-- Equal-size identity padding halves normalized squared Hilbert--Schmidt
distance. -/
theorem hsDistSq_padMatrix_card (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A B : Matrix Y Y ℂ) :
    hsDistSq (padModel Y (Fintype.card Y))
        (padMatrix Y (Fintype.card Y) A)
        (padMatrix Y (Fintype.card Y) B) = hsDistSq Y A B / 2 := by
  rw [hsDistSq_padMatrix]
  unfold hsDistSq
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp
  ring

/-- The normalized trace of equal-size identity padding is `(trace + 1) / 2`.
-/
theorem normTrace_padMatrix_card (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ) :
    normTrace (padModel Y (Fintype.card Y))
        (padMatrix Y (Fintype.card Y) A) = (normTrace Y A + 1) / 2 := by
  classical
  have hcard : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hY.ne'
  simp only [normTrace, Matrix.trace, Matrix.diag, padMatrix,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂]
  simp
  field_simp
  ring

/-- Pad a fixed-separation model by an equal identity block.  The result is a
non-scalar model with one quarter of the original separation parameter. -/
noncomputable def WeakHyperlinearModel.padToNonScalar
    {F : Finset G} {delta ε : ℝ} (M : WeakHyperlinearModel G F delta ε) :
    NonScalarModel G F ε (delta / 4) := by
  let d := Fintype.card M.carrier
  refine {
    carrier := padModel M.carrier d
    nonempty := by
      rw [card_padModel]
      exact Nat.add_pos_left M.nonempty d
    map := fun g ↦ padMatrix M.carrier d (M.map g)
    isUnitary := fun g ↦
      padMatrix_mem_unitaryGroup M.carrier d (M.isUnitary g)
    multiplicative := ?_
    nonScalar := ?_ }
  · intro g hg k hk
    rw [padMatrix_mul, hsDistSq_padMatrix_card M.carrier M.nonempty]
    have hnonneg : 0 ≤ hsDistSq M.carrier (M.map (g * k))
        (M.map g * M.map k) := by
      change 0 ≤ hsNormSq M.carrier (M.map (g * k) - M.map g * M.map k)
      exact hsNormSq_nonneg _ _
    exact (div_le_self hnonneg (by norm_num)).trans
      (M.multiplicative g hg k hk)
  · intro g hg k hk hgk
    let z : ℂ := normTrace M.carrier (M.map g * (M.map k)ᴴ)
    have hprod : M.map g * (M.map k)ᴴ ∈
        Matrix.unitaryGroup M.carrier ℂ := by
      exact Submonoid.mul_mem _ (M.isUnitary g)
        (by
          rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
            Matrix.conjTranspose_conjTranspose]
          have hkunitary := M.isUnitary k
          rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hkunitary
          exact hkunitary)
    have hzsq : Complex.normSq z ≤ 1 :=
      normSq_normTrace_le_one M.carrier hprod M.nonempty
    have hdist := M.separated g hg k hk hgk
    have hdistTrace := hsDistSq_of_unitary M.carrier (M.isUnitary g)
      (M.isUnitary k) M.nonempty
    have hzre : z.re ≤ 1 - delta / 2 := by
      rw [hdistTrace] at hdist
      change delta ≤ 2 - 2 * z.re at hdist
      linarith
    have hrelative :
        padMatrix M.carrier d (M.map g) *
            (padMatrix M.carrier d (M.map k))ᴴ =
          padMatrix M.carrier d (M.map g * (M.map k)ᴴ) := by
      rw [padMatrix_conjTranspose, padMatrix_mul]
    rw [hrelative, normTrace_padMatrix_card M.carrier M.nonempty]
    change Complex.normSq ((z + 1) / 2) ≤ 1 - delta / 4
    rw [Complex.normSq_div, Complex.normSq_add]
    norm_num
    change (Complex.normSq z + 1 + 2 * z.re) / 4 ≤ 1 - delta / 4
    linarith

/-- **Fixed positive tracial separation is enough for hyperlinearity.**

This is the elementary ultraproduct bridge needed by the Kazhdan-corner
argument.  Equal-size identity padding removes scalar phases, after which
conjugate-double tensor amplification drives separation to `2`.
-/
theorem isHyperlinear_of_isHyperlinearWeak {delta : ℝ} (hdelta : 0 < delta)
    (h : IsHyperlinearWeak G delta) : IsHyperlinear G := by
  apply isHyperlinear_of_isHyperlinearNonScalar
  intro F
  refine ⟨delta / 4, by positivity, ?_⟩
  intro ε hε
  obtain ⟨M⟩ := h F ε hε
  exact ⟨M.padToNonScalar⟩

end GroupApproximation
