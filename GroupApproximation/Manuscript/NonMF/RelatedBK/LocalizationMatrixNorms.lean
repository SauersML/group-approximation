import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Block
import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): matrix norm tools for the localization

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module holds the finite-matrix facts used to prove
`CoronaUCPFiniteCoordinateLocalizationStatement`. The proof route is in
`LocalizationTheorem`.

* `localization_exists_gram_of_quadForm_re_nonpos`: if the real part of the quadratic form of
  `H` is nonpositive, then `-(H + Hᴴ)` is a Gram matrix `star G * G`.
* Block entries of a matrix on `Z × W` are contractive in the `ℓ²` operator norm, and the norm
  of the whole matrix is at most the sum of the norms of its blocks.
* A block-diagonal matrix has norm at most any common bound on its blocks.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

noncomputable section

open scoped Matrix

open scoped MatrixOrder ComplexOrder in
/-- A matrix whose quadratic form has nonpositive real part gives a Gram matrix
`-(H + Hᴴ) = star G * G`. -/
theorem localization_exists_gram_of_quadForm_re_nonpos {Z : Type} [Fintype Z]
    (H : Matrix Z Z ℂ) (hH : ∀ x : Z → ℂ, (star x ⬝ᵥ (H *ᵥ x)).re ≤ 0) :
    ∃ G : Matrix Z Z ℂ, -(H + H.conjTranspose) = star G * G := by
  classical
  have hform : ∀ x : Z → ℂ, star x ⬝ᵥ ((-(H + H.conjTranspose)) *ᵥ x) =
      -(star x ⬝ᵥ (H *ᵥ x) + star (star x ⬝ᵥ (H *ᵥ x))) := by
    intro x
    rw [Matrix.neg_mulVec, Matrix.add_mulVec, dotProduct_neg, dotProduct_add,
      Matrix.dotProduct_mulVec (star x) H.conjTranspose x,
      Matrix.vecMul_conjTranspose H (star x), star_star x,
      Matrix.star_dotProduct (H *ᵥ x) x]
  have hpsd : (-(H + H.conjTranspose)).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_add_transpose_self H).neg fun x ↦ ?_
    rw [hform x]
    have hx := hH x
    refine Complex.nonneg_iff.2 ⟨?_, ?_⟩
    · rw [Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re]
      linarith
    · rw [Complex.neg_im, Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel,
        neg_zero]
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg

open scoped Matrix.Norms.L2Operator

/-- The `(l, i)` block of a matrix on `Z × W`. -/
def localizationBlockEntry {Z W : Type} (G : Matrix (Z × W) (Z × W) ℂ) (l i : Z) :
    Matrix W W ℂ :=
  Matrix.of fun a b ↦ G (l, a) (i, b)

@[simp]
theorem localizationBlockEntry_apply {Z W : Type} (G : Matrix (Z × W) (Z × W) ℂ) (l i : Z)
    (a b : W) : localizationBlockEntry G l i a b = G (l, a) (i, b) :=
  rfl

/-- Extend a vector on `W` to `Z × W` by placing it in column `i`. -/
def localizationColumnExtend {Z W : Type} [DecidableEq Z] (i : Z) (x : W → ℂ) : Z × W → ℂ :=
  fun p ↦ if p.1 = i then x p.2 else 0

theorem localizationBlockEntry_mulVec {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W]
    (G : Matrix (Z × W) (Z × W) ℂ) (l i : Z) (x : W → ℂ) (a : W) :
    (localizationBlockEntry G l i *ᵥ x) a =
      (G *ᵥ localizationColumnExtend i x) (l, a) := by
  simp only [Matrix.mulVec, dotProduct, localizationBlockEntry_apply, localizationColumnExtend,
    Fintype.sum_prod_type, mul_ite, mul_zero]
  symm
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem sum_normSq_localizationColumnExtend {Z W : Type} [Fintype Z] [DecidableEq Z]
    [Fintype W] (i : Z) (x : W → ℂ) :
    ∑ p, Complex.normSq (localizationColumnExtend i x p) = ∑ b, Complex.normSq (x b) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [localizationColumnExtend]
  · intro k _ hk
    simp [localizationColumnExtend, hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A block of a matrix has operator norm at most the norm of the matrix. -/
theorem norm_localizationBlockEntry_le {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W]
    [DecidableEq W] (G : Matrix (Z × W) (Z × W) ℂ) (l i : Z) :
    ‖localizationBlockEntry G l i‖ ≤ ‖G‖ := by
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg G)
    fun x ↦ ?_
  calc ∑ a, Complex.normSq ((localizationBlockEntry G l i *ᵥ x) a)
      = ∑ a, Complex.normSq ((G *ᵥ localizationColumnExtend i x) (l, a)) :=
        Finset.sum_congr rfl fun a _ ↦ by rw [localizationBlockEntry_mulVec]
    _ ≤ ∑ p, Complex.normSq ((G *ᵥ localizationColumnExtend i x) p) := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum
          (f := fun k ↦ ∑ a, Complex.normSq ((G *ᵥ localizationColumnExtend i x) (k, a)))
          (fun k _ ↦ Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ l)
    _ ≤ ‖G‖ ^ 2 * ∑ p, Complex.normSq (localizationColumnExtend i x p) :=
        KazhdanCornerMatrices.sum_normSq_mulVec_le_general G _
    _ = ‖G‖ ^ 2 * ∑ b, Complex.normSq (x b) := by
        rw [sum_normSq_localizationColumnExtend]

/-- Insert a `W × W` matrix as the `(i, j)` block of a matrix on `Z × W`. -/
def localizationBlockInsert {Z W : Type} [DecidableEq Z] (i j : Z) (M : Matrix W W ℂ) :
    Matrix (Z × W) (Z × W) ℂ :=
  Matrix.of fun p q ↦ if p.1 = i ∧ q.1 = j then M p.2 q.2 else 0

theorem localizationBlockInsert_mulVec {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W]
    (i j : Z) (M : Matrix W W ℂ) (x : Z × W → ℂ) (p : Z × W) :
    (localizationBlockInsert i j M *ᵥ x) p =
      if p.1 = i then (M *ᵥ fun b ↦ x (j, b)) p.2 else 0 := by
  simp only [Matrix.mulVec, dotProduct, localizationBlockInsert, Matrix.of_apply,
    Fintype.sum_prod_type]
  by_cases hp : p.1 = i
  · rw [if_pos hp, Finset.sum_eq_single j]
    · simp [hp]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · simp [hp]

theorem norm_localizationBlockInsert_le {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W]
    [DecidableEq W] (i j : Z) (M : Matrix W W ℂ) :
    ‖localizationBlockInsert i j M‖ ≤ ‖M‖ := by
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg M)
    fun x ↦ ?_
  calc ∑ p, Complex.normSq ((localizationBlockInsert i j M *ᵥ x) p)
      = ∑ b, Complex.normSq ((M *ᵥ fun b ↦ x (j, b)) b) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
        · simp [localizationBlockInsert_mulVec]
        · intro k _ hk
          simp [localizationBlockInsert_mulVec, hk]
        · intro h
          exact absurd (Finset.mem_univ i) h
    _ ≤ ‖M‖ ^ 2 * ∑ b, Complex.normSq (x (j, b)) :=
        KazhdanCornerMatrices.sum_normSq_mulVec_le_general M _
    _ ≤ ‖M‖ ^ 2 * ∑ p, Complex.normSq (x p) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun k ↦ ∑ b, Complex.normSq (x (k, b)))
          (fun k _ ↦ Finset.sum_nonneg fun b _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ j)

theorem localization_eq_sum_blockInsert {Z W : Type} [Fintype Z] [DecidableEq Z]
    (H : Matrix (Z × W) (Z × W) ℂ) :
    H = ∑ i, ∑ j, localizationBlockInsert i j (localizationBlockEntry H i j) := by
  ext p q
  simp only [Matrix.sum_apply, localizationBlockInsert, Matrix.of_apply,
    localizationBlockEntry_apply]
  rw [Finset.sum_eq_single p.1, Finset.sum_eq_single q.1]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ q.1) h
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ p.1) h

/-- The norm of a matrix on `Z × W` is at most the sum of the norms of its blocks. -/
theorem norm_le_sum_localizationBlockEntry {Z W : Type} [Fintype Z] [DecidableEq Z]
    [Fintype W] [DecidableEq W] (H : Matrix (Z × W) (Z × W) ℂ) :
    ‖H‖ ≤ ∑ i, ∑ j, ‖localizationBlockEntry H i j‖ := by
  calc ‖H‖ = ‖∑ i, ∑ j, localizationBlockInsert i j (localizationBlockEntry H i j)‖ := by
        rw [← localization_eq_sum_blockInsert H]
    _ ≤ ∑ i, ‖∑ j, localizationBlockInsert i j (localizationBlockEntry H i j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖localizationBlockEntry H i j‖ :=
        Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ ↦ norm_localizationBlockInsert_le i j _)

/-- A block-diagonal matrix acts on a vector blockwise. -/
theorem localization_blockDiagonal'_mulVec {o : Type} [Fintype o] [DecidableEq o]
    {m' : o → Type} [∀ i, Fintype (m' i)] (M : ∀ i, Matrix (m' i) (m' i) ℂ)
    (v : (Σ i, m' i) → ℂ) (i : o) (k : m' i) :
    (Matrix.blockDiagonal' M *ᵥ v) ⟨i, k⟩ = (M i *ᵥ fun j ↦ v ⟨i, j⟩) k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma (fun x : Σ i, m' i ↦ Matrix.blockDiagonal' M ⟨i, k⟩ x * v x)]
  rw [Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun j _ ↦ by rw [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A block-diagonal matrix has norm at most any common bound on its blocks. -/
theorem norm_localization_blockDiagonal'_le {o : Type} [Fintype o] [DecidableEq o]
    {m' : o → Type} [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)]
    (M : ∀ i, Matrix (m' i) (m' i) ℂ) {c : ℝ} (hc : 0 ≤ c) (hM : ∀ i, ‖M i‖ ≤ c) :
    ‖Matrix.blockDiagonal' M‖ ≤ c := by
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general _ hc fun v ↦ ?_
  calc ∑ p, Complex.normSq ((Matrix.blockDiagonal' M *ᵥ v) p)
      = ∑ i, ∑ k, Complex.normSq ((M i *ᵥ fun j ↦ v ⟨i, j⟩) k) := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by
          rw [localization_blockDiagonal'_mulVec]
    _ ≤ ∑ i, c ^ 2 * ∑ k, Complex.normSq (v ⟨i, k⟩) :=
        Finset.sum_le_sum fun i _ ↦
          (KazhdanCornerMatrices.sum_normSq_mulVec_le_general (M i) _).trans
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM i) 2)
              (Finset.sum_nonneg fun k _ ↦ Complex.normSq_nonneg _))
    _ = c ^ 2 * ∑ p, Complex.normSq (v p) := by
        rw [Fintype.sum_sigma, Finset.mul_sum]

end

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms localization_exists_gram_of_quadForm_re_nonpos
#audit_axioms localizationBlockEntry
#audit_axioms localizationBlockEntry_apply
#audit_axioms localizationColumnExtend
#audit_axioms localizationBlockEntry_mulVec
#audit_axioms sum_normSq_localizationColumnExtend
#audit_axioms norm_localizationBlockEntry_le
#audit_axioms localizationBlockInsert
#audit_axioms localizationBlockInsert_mulVec
#audit_axioms norm_localizationBlockInsert_le
#audit_axioms localization_eq_sum_blockInsert
#audit_axioms norm_le_sum_localizationBlockEntry
#audit_axioms localization_blockDiagonal'_mulVec
#audit_axioms norm_localization_blockDiagonal'_le
