import GroupApproximation.KOne.AryPencilCore
import GroupApproximation.KOne.BalancedRegularity
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank normal form and regularity of the balanced subalgebra, at arbitrary arity

`Leavitt/RankNormalForm.lean` and `KOne/BalancedRegularity.lean` over a complete matrix
family `F` on an alphabet `ι`.  The balanced span at depth `n` is the image of
`M_{ι^n}(k)` under `(F.powerFamily n).matrixEmbedding`, a ring homomorphism, so:

* every balanced element is `g⁻¹·e·h⁻¹` for balanced units `g, h` and a cylinder-sum
  idempotent `e`, with `e = 1` in the invertible case (`exists_rank_normal_form`);
* a balanced element that is a unit has a balanced inverse
  (`inv_mem_levelSpan_of_val_mem`);
* every balanced element has a balanced pseudo-inverse (`exists_balanced_pseudoInverse`),
  hence square-zero tails `1 + sᵢ z` die (`square_zero_tail_mem_stableUnits`).

The binary files transport along `balancedEmbed`; here the embedding is the family's own
`matrixEmbedding`, so no prefix-code layer is involved.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

/-- Every balanced element is the depth-`n` embedding of a scalar matrix. -/
theorem exists_matrixEmbedding_eq {n : ℕ} {x : A}
    (hx : x ∈ Submodule.span k (F.levelMonomialSet n)) :
    ∃ C : Matrix (Fin n → ι) (Fin n → ι) k, (F.powerFamily n).matrixEmbedding C = x := by
  classical
  have hentry : ∀ γ δ : Fin n → ι, ∃ c : k,
      algebraMap k A c = (F.powerFamily n).right γ * x * (F.powerFamily n).left δ := by
    intro γ δ
    obtain ⟨c, hc⟩ := F.entry_mem_range_algebraMap (k := k) n hx γ δ
    exact ⟨c, hc⟩
  choose C hC using hentry
  refine ⟨Matrix.of C, ?_⟩
  have hmat : (algebraMap k A).mapMatrix (Matrix.of C) =
      (F.powerFamily n).matrixRingEquiv.symm x := by
    ext γ δ
    rw [matrixRingEquiv_symm_apply]
    exact hC γ δ
  show (F.powerFamily n).matrixRingEquiv ((algebraMap k A).mapMatrix (Matrix.of C)) = x
  rw [hmat, RingEquiv.apply_symm_apply]

/-- The scalar-matrix embedding sends diagonal matrices to weighted cylinder sums. -/
theorem matrixEmbedding_diagonal (n : ℕ) (dv : (Fin n → ι) → k) :
    (F.powerFamily n).matrixEmbedding (Matrix.diagonal dv) =
      ∑ γ : Fin n → ι, dv γ • F.cylinder (List.ofFn γ) := by
  classical
  rw [matrixEmbedding_apply]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [Finset.sum_eq_single γ]
  · rw [Matrix.diagonal_apply_eq, powerFamily_left, powerFamily_right, cylinder,
      show F.wordS (List.ofFn γ) * algebraMap k A (dv γ) =
        algebraMap k A (dv γ) * F.wordS (List.ofFn γ) from (Algebra.commutes _ _).symm,
      mul_assoc, ← Algebra.smul_def]
  · intro δ _ hδ
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hδ), map_zero, mul_zero, zero_mul]
  · intro hγ
    exact absurd (Finset.mem_univ γ) hγ

/-- Indicator diagonals map to cylinder sums. -/
theorem matrixEmbedding_indicator (n : ℕ) (S : Finset (Fin n → ι)) :
    (F.powerFamily n).matrixEmbedding
      (Matrix.diagonal fun γ ↦ if γ ∈ S then (1 : k) else 0) =
      ∑ γ ∈ S, F.cylinder (List.ofFn γ) := by
  classical
  rw [F.matrixEmbedding_diagonal]
  have hsw : ∀ γ : Fin n → ι,
      (if γ ∈ S then (1 : k) else 0) • F.cylinder (List.ofFn γ) =
        (if γ ∈ S then F.cylinder (List.ofFn γ) else 0) := by
    intro γ
    split_ifs <;> simp
  simp only [hsw]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- A balanced element that is a unit has an invertible matrix. -/
theorem isUnit_matrix_of_isUnit [Nontrivial A] {n : ℕ}
    {C : Matrix (Fin n → ι) (Fin n → ι) k}
    (hu : IsUnit ((F.powerFamily n).matrixEmbedding C)) : IsUnit C := by
  classical
  by_contra hC
  have hdet : C.det = 0 := by
    by_contra hdt
    exact hC ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hdt))
  obtain ⟨v, hv, hCv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  set X : Matrix (Fin n → ι) (Fin n → ι) k := Matrix.of fun i _ ↦ v i with hX
  have hCX : C * X = 0 := by
    ext i j
    have := congrFun hCv i
    simpa [hX, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hXne : X ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro h0
    apply hi
    have h1 : X i i = (0 : Matrix (Fin n → ι) (Fin n → ι) k) i i := by rw [h0]
    simpa [hX] using h1
  have hxne : (F.powerFamily n).matrixEmbedding X ≠ 0 := by
    intro h0
    exact hXne ((F.powerFamily n).matrixEmbedding_injective (k := k)
      (h0.trans (map_zero _).symm))
  obtain ⟨u, huval⟩ := hu
  have hzero : (F.powerFamily n).matrixEmbedding C *
      (F.powerFamily n).matrixEmbedding X = 0 := by
    rw [← map_mul, hCX, map_zero]
  apply hxne
  calc (F.powerFamily n).matrixEmbedding X
      = ((u⁻¹ : Aˣ) : A) * ((u : A) * (F.powerFamily n).matrixEmbedding X) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ((u⁻¹ : Aˣ) : A) *
          ((F.powerFamily n).matrixEmbedding C * (F.powerFamily n).matrixEmbedding X) := by
        rw [huval]
    _ = 0 := by rw [hzero, mul_zero]

/-- **Balanced units have balanced inverses.** -/
theorem inv_mem_levelSpan_of_val_mem [Nontrivial A] {n : ℕ} (u : Aˣ)
    (hval : (u : A) ∈ Submodule.span k (F.levelMonomialSet n)) :
    ((u⁻¹ : Aˣ) : A) ∈ Submodule.span k (F.levelMonomialSet n) := by
  obtain ⟨C, hC⟩ := F.exists_matrixEmbedding_eq hval
  have hCu : IsUnit C := F.isUnit_matrix_of_isUnit (n := n) (hC.symm ▸ ⟨u, rfl⟩)
  obtain ⟨Cu, hCuval⟩ := hCu
  have hone : (u : A) * (F.powerFamily n).matrixEmbedding
      ((Cu⁻¹ : (Matrix (Fin n → ι) (Fin n → ι) k)ˣ) : Matrix (Fin n → ι) (Fin n → ι) k) =
        1 := by
    rw [← hC, ← hCuval, ← map_mul, Units.mul_inv, map_one]
  have hinv : ((u⁻¹ : Aˣ) : A) = (F.powerFamily n).matrixEmbedding
      ((Cu⁻¹ : (Matrix (Fin n → ι) (Fin n → ι) k)ˣ) :
        Matrix (Fin n → ι) (Fin n → ι) k) := by
    calc ((u⁻¹ : Aˣ) : A)
        = ((u⁻¹ : Aˣ) : A) * ((u : A) * (F.powerFamily n).matrixEmbedding
            ((Cu⁻¹ : (Matrix (Fin n → ι) (Fin n → ι) k)ˣ) :
              Matrix (Fin n → ι) (Fin n → ι) k)) := by
          rw [hone, mul_one]
      _ = (F.powerFamily n).matrixEmbedding
            ((Cu⁻¹ : (Matrix (Fin n → ι) (Fin n → ι) k)ˣ) :
              Matrix (Fin n → ι) (Fin n → ι) k) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hinv]
  exact F.matrixEmbedding_mem_levelSpan n _

/-- **Rank normal form**: every balanced element is equivalent, via balanced units with
balanced inverses, to a cylinder-sum idempotent; full support certifies invertibility. -/
theorem exists_rank_normal_form {n : ℕ} {c : A}
    (hc : c ∈ Submodule.span k (F.levelMonomialSet n)) :
    ∃ (g h : Aˣ) (S : Finset (Fin n → ι)),
      (g : A) ∈ Submodule.span k (F.levelMonomialSet n) ∧
      ((g⁻¹ : Aˣ) : A) ∈ Submodule.span k (F.levelMonomialSet n) ∧
      (h : A) ∈ Submodule.span k (F.levelMonomialSet n) ∧
      ((h⁻¹ : Aˣ) : A) ∈ Submodule.span k (F.levelMonomialSet n) ∧
      (g : A) * c * (h : A) = ∑ γ ∈ S, F.cylinder (List.ofFn γ) ∧
      (S = Finset.univ → IsUnit c) := by
  classical
  obtain ⟨C, hC⟩ := F.exists_matrixEmbedding_eq hc
  obtain ⟨Lt, Lt', dvec, hCdec⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  set P : Matrix (Fin n → ι) (Fin n → ι) k :=
    (Lt.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q : Matrix (Fin n → ι) (Fin n → ι) k :=
    (Lt'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have hPunit : IsUnit P := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det P).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  have hQunit : IsUnit Q := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt'
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det Q).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  set D₁ : Matrix (Fin n → ι) (Fin n → ι) k :=
    Matrix.diagonal (fun γ ↦ if dvec γ = 0 then 1 else dvec γ) with hD₁
  set S : Finset (Fin n → ι) := Finset.univ.filter (fun γ ↦ dvec γ ≠ 0) with hS
  set E : Matrix (Fin n → ι) (Fin n → ι) k :=
    Matrix.diagonal (fun γ ↦ if γ ∈ S then (1 : k) else 0) with hE
  have hD₁unit : IsUnit D₁ := by
    refine (Matrix.isUnit_iff_isUnit_det D₁).mpr ?_
    rw [hD₁, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr ?_)
    intro γ _
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have hDE : Matrix.diagonal dvec = D₁ * E := by
    rw [hD₁, hE, Matrix.diagonal_mul_diagonal]
    congr 1
    funext γ
    by_cases h : dvec γ = 0
    · rw [if_pos h, if_neg (by simp [hS, h]), mul_zero, h]
    · rw [if_neg h, if_pos (by simp [hS, h]), mul_one]
  obtain ⟨Pu, hPu⟩ := hPunit.mul hD₁unit
  obtain ⟨Qu, hQu⟩ := hQunit
  refine ⟨Units.map ((F.powerFamily n).matrixEmbedding (k := k)).toMonoidHom Pu⁻¹,
    Units.map ((F.powerFamily n).matrixEmbedding (k := k)).toMonoidHom Qu⁻¹, S,
    F.matrixEmbedding_mem_levelSpan n _, ?_, F.matrixEmbedding_mem_levelSpan n _,
    ?_, ?_, ?_⟩
  · rw [Units.coe_map_inv]
    exact F.matrixEmbedding_mem_levelSpan n _
  · rw [Units.coe_map_inv]
    exact F.matrixEmbedding_mem_levelSpan n _
  · show (F.powerFamily n).matrixEmbedding
        ((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) * c *
      (F.powerFamily n).matrixEmbedding ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) = _
    rw [← hC, ← map_mul, ← map_mul, ← F.matrixEmbedding_indicator (k := k) n S, ← hE]
    congr 1
    have hCform : C = (P * D₁) * (E * Q) := by
      rw [hCdec, hDE]
      noncomm_ring
    rw [hCform, ← hPu, ← hQu]
    calc ((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) *
          ((Pu : Matrix _ _ k) * (E * (Qu : Matrix _ _ k))) *
          ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k)
        = (((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) * (Pu : Matrix _ _ k)) * E *
          ((Qu : Matrix _ _ k) * ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k)) := by
          noncomm_ring
      _ = E := by rw [Units.inv_mul, Units.mul_inv, one_mul, mul_one]
  · intro hSuniv
    have hEone : E = 1 := by
      rw [hE, hSuniv]
      simp [Matrix.diagonal_one]
    have hCunit : IsUnit C := by
      rw [hCdec, hDE, hEone, mul_one]
      exact (hPunit.mul hD₁unit).mul ⟨Qu, hQu⟩
    rw [← hC]
    exact hCunit.map ((F.powerFamily n).matrixEmbedding (k := k))

/-- **Balanced regularity**: every balanced element has a balanced pseudo-inverse. -/
theorem exists_balanced_pseudoInverse {n : ℕ} {z : A}
    (hz : z ∈ Submodule.span k (F.levelMonomialSet n)) :
    ∃ ξ : A, ξ ∈ Submodule.span k (F.levelMonomialSet n) ∧ z * ξ * z = z := by
  obtain ⟨C, hC⟩ := F.exists_matrixEmbedding_eq hz
  obtain ⟨X, hX⟩ := exists_pseudoInverse_matrix C
  refine ⟨(F.powerFamily n).matrixEmbedding X, F.matrixEmbedding_mem_levelSpan n X, ?_⟩
  rw [← hC, ← map_mul, ← map_mul, hX]

/-- **Square-zero tails die**: if `(sᵢ z)² = 0` with `z` balanced, then any unit of
value `1 + sᵢ z` lies in the stably elementary subgroup. -/
theorem square_zero_tail_mem_stableUnits {n : ℕ} (i : ι) {z : A}
    (hz : z ∈ Submodule.span k (F.levelMonomialSet n))
    (hsq : F.left i * z * (F.left i * z) = 0) (u : Aˣ)
    (hu : (u : A) = 1 + F.left i * z) :
    u ∈ stableUnits A := by
  obtain ⟨ξ, _, hξ⟩ := F.exists_balanced_pseudoInverse hz
  have hts : F.right i * F.left i = 1 := by rw [F.orthogonal, if_pos rfl]
  have hzsz : z * (F.left i * z) = 0 := by
    have h1 : F.right i * (F.left i * z * (F.left i * z)) = 0 := by rw [hsq, mul_zero]
    rwa [show F.right i * (F.left i * z * (F.left i * z)) =
      (F.right i * F.left i) * (z * (F.left i * z)) from by noncomm_ring,
      hts, one_mul] at h1
  refine mem_stableUnits_of_val_unipotent (F.left i * z) (ξ * z) ?_ ?_
  · rw [show ξ * z * (F.left i * z) = ξ * (z * (F.left i * z)) from by noncomm_ring,
      hzsz, mul_zero]
  · rw [hu]
    congr 1
    rw [show F.left i * z * (ξ * z) = F.left i * (z * ξ * z) from by noncomm_ring, hξ]

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_matrixEmbedding_eq
#audit_axioms GroupApproximation.CompleteMatrixFamily.matrixEmbedding_diagonal
#audit_axioms GroupApproximation.CompleteMatrixFamily.isUnit_matrix_of_isUnit
#audit_axioms GroupApproximation.CompleteMatrixFamily.inv_mem_levelSpan_of_val_mem
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_rank_normal_form
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_balanced_pseudoInverse
#audit_axioms GroupApproximation.CompleteMatrixFamily.square_zero_tail_mem_stableUnits
