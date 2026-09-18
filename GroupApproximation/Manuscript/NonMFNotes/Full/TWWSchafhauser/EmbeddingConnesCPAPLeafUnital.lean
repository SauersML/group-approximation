import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesCPAPLeafSchwarz
import GroupApproximation.Analysis.LanceForward
import GroupApproximation.Analysis.LanceCPContractiveUnitalization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.FormPositivity

/-!
# Connes' trick, CPAP leaf: unital completely positive matrix approximations

Lane TWWSch3b1A (work order WO-3b1-A).  Second leaf of
`isMatrixLeftBimoduleCPAP_of_isNuclearCStarAlgebra`, which feeds the Tikuisis--White--Winter
input `\cite{TWW}` of `non_mf_group_notes.tex` (quasidiagonality of nuclear C⋆-algebras), used in
the proof of `thm:fixed-radical-membership`.
Sources: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Prop 2.2.6 and the
proof of Thm 6.2.7.

* `exists_ucpMatrixApproximation`: a nontrivial nuclear C⋆-algebra has, on every finite set and
  at every tolerance, *unital* completely positive maps `ρ : A → M_Y` and `ψ : M_Y → A` with
  `ψ ∘ ρ ≈ id`.  The contractive matrix models of `Analysis/LanceForward` are repaired by the
  additive unitalization of `Analysis/LanceCPContractiveUnitalization`; its error bound is stated
  on the unit ball, so the finite set is first rescaled.
* `cpap_isCompletelyPositiveOnMatrices_of_isCompletelyPositive`: a completely positive map into
  a matrix block is completely positive in the form sense of `Analysis/QuasidiagonalTrace`.
* `cpap_vecMulVec_eq_star_mul_self`: rank-one projections `v v⋆` are of the form `N⋆ N`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open CStarExactness Quasidiagonal
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

attribute [local instance] CStarExactness.matrixBlockCStarAlgebraForLanceForward

/-! ## From matrix complete positivity to form complete positivity -/

/-- Reindexing to `Fin (card Y)` followed by the operator picture, as a `⋆`-homomorphism. -/
def cpapEuclideanizeStarHom (Y : FiniteModel) :
    Matrix Y Y ℂ →⋆ₙₐ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) :=
  ((Matrix.toEuclideanCLM (𝕜 := ℂ)).toStarAlgHom.comp
    (matrixReindexStarAlgEquiv (Quasidiagonal.enum Y)).toStarAlgHom).toNonUnitalStarAlgHom

/-- The operator picture of a matrix block is completely positive. -/
theorem cpap_isCompletelyPositive_euclideanize (Y : FiniteModel) [Nonempty Y] :
    IsCompletelyPositive (Quasidiagonal.euclideanize Y) := by
  have hEq : Quasidiagonal.euclideanize Y =
      (cpapEuclideanizeStarHom Y : Matrix Y Y ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Fintype.card Y)))) :=
    LinearMap.ext fun _ ↦ rfl
  rw [hEq]
  exact isCompletelyPositive_of_starAlgHom (cpapEuclideanizeStarHom Y)

/-- **Matrix complete positivity gives form complete positivity** (Brown--Ozawa, Prop 1.5.12
in the matrix picture).  Pass to operators on `ℓ²(Fin (card Y))`, where the form statement is
`A2LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean`, and come back. -/
theorem cpap_isCompletelyPositiveOnMatrices_of_isCompletelyPositive {A : Type u}
    [CStarAlgebra A] (Y : FiniteModel) [Nonempty Y] (ψ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (hψ : IsCompletelyPositive ψ) : IsCompletelyPositiveOnMatrices Y ⇑ψ := by
  have hform := A2LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean Y
    (Quasidiagonal.euclideanize Y ∘ₗ ψ) ((cpap_isCompletelyPositive_euclideanize Y).comp hψ)
  have hfun : (fun a ↦ A2LocalLifting.matrixOfEuclidean Y
      ((Quasidiagonal.euclideanize Y ∘ₗ ψ) a)) = ⇑ψ := by
    funext a
    exact A2LocalLifting.matrixOfEuclidean_euclideanize Y (ψ a)
  rw [← hfun]
  exact hform

/-- A rank-one matrix `v v⋆` is `N⋆ N` for the matrix `N` whose only nonzero row is `v⋆`. -/
theorem cpap_vecMulVec_eq_star_mul_self {Y : Type} [Fintype Y] [DecidableEq Y] (y₀ : Y)
    (v : Y → ℂ) :
    Matrix.vecMulVec v (star v) =
      star (Matrix.of fun i j ↦ if i = y₀ then star (v j) else 0 : Matrix Y Y ℂ) *
        (Matrix.of fun i j ↦ if i = y₀ then star (v j) else 0 : Matrix Y Y ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.sum_eq_single y₀]
  · simp [Matrix.star_apply]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ y₀) h

/-! ## Unital completely positive matrix approximations -/

/-- **Nuclear algebras have ucp matrix approximations** (Brown--Ozawa, Prop 2.2.6 and the proof
of Thm 6.2.7, via the additive unitalization).  For a nontrivial nuclear `A`, every finite set
`F` and every `ε > 0`, there are unital completely positive `ρ : A → M_Y` and `ψ : M_Y → A` with
`‖ψ (ρ a) - a‖ ≤ ε` on `F`. -/
theorem exists_ucpMatrixApproximation {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (hnuc : IsNuclearCStarAlgebra A) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A),
        IsCompletelyPositive ρ ∧ ρ 1 = 1 ∧ IsCompletelyPositive ψ ∧ ψ 1 = 1 ∧
          ∀ a ∈ F, ‖ψ (ρ a) - a‖ ≤ ε := by
  classical
  obtain ⟨R, hR0, hRF⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ a ∈ F, ‖a‖ ≤ R :=
    ⟨∑ a ∈ F, ‖a‖, Finset.sum_nonneg fun b _ ↦ norm_nonneg b,
      fun a ha ↦ Finset.single_le_sum (f := fun b ↦ ‖b‖) (fun b _ ↦ norm_nonneg b) ha⟩
  have hR1 : 0 < R + 1 := by linarith
  have hδ : 0 < ε / (4 * (R + 1)) := div_pos hε (by positivity)
  let t : ℂ := ((R + 1 : ℝ) : ℂ)
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr hR1.ne'
  have hnorm_t : ‖t‖ = R + 1 := Complex.norm_of_nonneg hR1.le
  let G : Finset A := insert 1 (F.image fun a ↦ t⁻¹ • a)
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdownC, hupC, hrec⟩ :=
    exists_matrixModelApproximation_of_isNuclearCStarAlgebra hnuc G
      (ε / (4 * (R + 1))) hδ
  letI : Nonempty Y := hY
  let omegaA : CStarState.State A :=
    (CStarState.State.exists_star_mul_self (1 : A)).choose
  let omegaY : CStarState.State (Matrix Y Y ℂ) :=
    (CStarState.State.exists_star_mul_self (1 : Matrix Y Y ℂ)).choose
  obtain ⟨hρCP, hρ1⟩ :=
    additiveUnitalization_completelyPositive_unital down omegaA hdownCP hdownC
  obtain ⟨hψCP, hψ1⟩ :=
    additiveUnitalization_completelyPositive_unital up omegaY hupCP hupC
  refine ⟨Y, hY, additiveUnitalization down omegaA, additiveUnitalization up omegaY,
    hρCP, hρ1, hψCP, hψ1, ?_⟩
  intro a ha
  have hone : ‖up (down 1) - 1‖ ≤ ε / (4 * (R + 1)) := hrec 1 (Finset.mem_insert_self 1 _)
  have hbmem : t⁻¹ • a ∈ G :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hb : ‖t⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hnorm_t, inv_mul_le_iff₀ hR1, mul_one]
    linarith [hRF a ha]
  have h4 := norm_additiveUnitalization_comp_sub_le_four_mul down up omegaA omegaY
    hdownCP hupCP hdownC hupC hone (t⁻¹ • a) hb (hrec _ hbmem)
  have hlin : additiveUnitalization up omegaY (additiveUnitalization down omegaA a) - a =
      t • (additiveUnitalization up omegaY (additiveUnitalization down omegaA (t⁻¹ • a)) -
        t⁻¹ • a) := by
    rw [map_smul, map_smul, ← smul_sub, smul_inv_smul₀ ht]
  have hkey : (R + 1) * (4 * (ε / (4 * (R + 1)))) = ε := by
    rw [← mul_assoc, mul_comm (R + 1) 4, mul_div_cancel₀ ε (by positivity)]
  rw [hlin, norm_smul, hnorm_t, ← hkey]
  exact mul_le_mul_of_nonneg_left h4 hR1.le

end

end TWWSchafhauser
end Full
end GroupApproximation
