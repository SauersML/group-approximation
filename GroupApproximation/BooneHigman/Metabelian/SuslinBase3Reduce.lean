import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: both directions of the reduction to the stabilized residual

Lane `bh-met-91b`.

* `suslinBase3_blockLocal_of_stab`: suppose `A → A_𝔪` is injective for every maximal `𝔪`.
  Then `SuslinBase3StabLocal A n` gives `SuslinR2BlockLocal A (n + 1)`.

  **Proof.**  Write `T = τ_𝔪 F`, a normalized coordinate block.  Up to reindexing,
  `T = diag(σ, 1)` with `σ ∈ SL_n(A_𝔪[X])` and `σ(0) = 1` (as in `suslinR2Ind_block_mem`).
  Clear the denominators of `σ` and `σ⁻¹` by one `s ∉ 𝔪`.  The dilation `σ(sX)` lifts to a
  normalized `τ' ∈ SL_n(A[X])` (`suslinR2Ind_lift_matrix`).  The residual gives
  `diag(σ(sX), 1) ∈ E_{n+1}`.  Undoing the dilation (`suslinR2Ind_mem_of_dilate`) gives
  `diag(σ, 1) ∈ E_{n+1}`, so `T ∈ E_{n+1}` and `τ_𝔪 = T F⁻¹ ∈ E_{n+1}`.

* `suslinBase3_stab_of_blockLocal`: the converse, with no hypothesis on `A`.  Take
  `τ = diag(σ, 1)` reindexed, `F = 1` and `r` the extra coordinate.

So the residual is logically EQUIVALENT to the block form at the next rank whenever
`A → A_𝔪` is injective.  What it removes is proof content: the factor `F`, the coordinate
block, the reindexing and all localized denominators.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Normalized local matrices stabilize into `E_{n+1}`**, given the residual at rank `n` and
injectivity of `A → A_𝔪`. -/
theorem suslinBase3_stab_mem {A : Type*} [CommRing A] {n : ℕ}
    (h : SuslinBase3StabLocal A n) (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal)
    (hf : Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (σ : (Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) = 1)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := Localization.AtPrime 𝔪)) σ =
      1) :
    stabilizeUnit (R := (Localization.AtPrime 𝔪)[X]) (κ := Unit) σ ∈
      elementaryGroup (Fin n ⊕ Unit) (Localization.AtPrime 𝔪)[X] := by
  obtain ⟨s, hs, q, hq⟩ := suslinR2Ind_common_denom 𝔪.primeCompl
    (Sum.elim
      (fun ij : Fin n × Fin n ↦
        (σ : Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) ij.1 ij.2)
      (fun ij : Fin n × Fin n ↦
        ((σ⁻¹ : (Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X])ˣ) :
          Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) ij.1 ij.2))
  have h0i : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := Localization.AtPrime 𝔪))
      σ⁻¹ = 1 := by
    rw [map_inv, h0, inv_one]
  obtain ⟨P, hP, hP0⟩ := suslinR2Ind_lift_matrix (algebraMap A (Localization.AtPrime 𝔪)) σ h0
    s (fun i j ↦ q (Sum.inl (i, j))) (fun i j ↦ hq (Sum.inl (i, j)))
  obtain ⟨Q, hQ, -⟩ := suslinR2Ind_lift_matrix (algebraMap A (Localization.AtPrime 𝔪)) σ⁻¹ h0i
    s (fun i j ↦ q (Sum.inr (i, j))) (fun i j ↦ hq (Sum.inr (i, j)))
  have hPQ : P * Q = 1 := suslinR2Ind_mapMatrix_injective hf _ _ (by
    rw [map_mul, hP, hQ, ← map_mul, Units.mul_inv, map_one, map_one])
  have hQP : Q * P = 1 := suslinR2Ind_mapMatrix_injective hf _ _ (by
    rw [map_mul, hP, hQ, ← map_mul, Units.inv_mul, map_one, map_one])
  let τ' : (Matrix (Fin n) (Fin n) A[X])ˣ := ⟨P, Q, hPQ, hQP⟩
  have hdet' : Matrix.det (τ' : Matrix (Fin n) (Fin n) A[X]) = 1 := by
    apply Polynomial.map_injective (algebraMap A (Localization.AtPrime 𝔪)) hf
    change mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) (Matrix.det P) =
      mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) 1
    rw [RingHom.map_det, hP, ← RingHom.map_det, hdet, map_one, map_one]
  have hτ0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) τ' = 1 := by
    apply Units.ext
    ext i j
    change Polynomial.constantCoeff (P i j) = (1 : Matrix (Fin n) (Fin n) A) i j
    rw [Polynomial.constantCoeff_apply, hP0]
  have hmem := h τ' hdet' hτ0 𝔪 h𝔪
  have heq : elementaryMatrixUnitMap (ι := Fin n)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ' =
      elementaryMatrixUnitMap (compRingHom (C (algebraMap A (Localization.AtPrime 𝔪) s) * X))
        σ := by
    apply Units.ext
    exact hP
  rw [heq, ← suslinBase3_map_stabilize
    (compRingHom (C (algebraMap A (Localization.AtPrime 𝔪) s) * X)) σ] at hmem
  obtain ⟨c, hc⟩ :=
    (IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨s, hs⟩ : 𝔪.primeCompl)).exists_right_inv
  exact suslinR2Ind_mem_of_dilate hc _ hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_stab_mem

/-- **Normalized coordinate blocks are elementary** at rank `n + 1`, given that `diag(σ, 1)` is
elementary for every normalized `σ ∈ SL_n(B[X])`. -/
theorem suslinBase3_block_mem {B : Type*} [CommRing B] {n : ℕ}
    (hσ : ∀ σ : (Matrix (Fin n) (Fin n) B[X])ˣ,
      Matrix.det (σ : Matrix (Fin n) (Fin n) B[X]) = 1 →
        elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) σ = 1 →
          stabilizeUnit (R := B[X]) (κ := Unit) σ ∈ elementaryGroup (Fin n ⊕ Unit) B[X])
    (T : (Matrix (Fin (n + 1)) (Fin (n + 1)) B[X])ˣ) (r : Fin (n + 1))
    (hT : T ∈ coordinateBlock B[X] r)
    (hdet : Matrix.det (T : Matrix (Fin (n + 1)) (Fin (n + 1)) B[X]) = 1)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) T = 1) :
    T ∈ elementaryGroup (Fin (n + 1)) B[X] := by
  obtain ⟨e, he⟩ : ∃ e : Fin n ⊕ Unit ≃ Fin (n + 1), e (Sum.inr ()) = r :=
    ⟨((finSuccEquiv' r).trans (Equiv.optionEquivSumPUnit (Fin n))).symm, by
      rw [Equiv.symm_trans_apply, Equiv.optionEquivSumPUnit_symm_inr,
        finSuccEquiv'_symm_none]⟩
  have hrange := range_reindexedStabilize_eq_coordinateBlock (R := B[X]) e
  rw [he] at hrange
  rw [← hrange] at hT
  obtain ⟨σ, hσT⟩ := MonoidHom.mem_range.mp hT
  have hTe : T = elementaryReindexUnitEquiv (R := B[X]) e
      (stabilizeUnit (R := B[X]) (κ := Unit) σ) := hσT.symm
  subst hTe
  have hdσ : Matrix.det (σ : Matrix (Fin n) (Fin n) B[X]) = 1 := by
    have h := hdet
    change Matrix.det ((Matrix.reindexRingEquiv B[X] e)
      (Matrix.fromBlocks (σ : Matrix (Fin n) (Fin n) B[X]) 0 0 1)) = 1 at h
    rw [Matrix.coe_reindexRingEquiv, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one] at h
    exact h
  have hσ0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) σ = 1 := by
    apply Units.ext
    ext i j
    have h := suslinR2Ind_coeff_zero _ h0 (e (Sum.inl i)) (e (Sum.inl j))
    rw [suslinR2Ind_reindex_stab_apply] at h
    change Polynomial.constantCoeff ((σ : Matrix (Fin n) (Fin n) B[X]) i j) = _
    rw [Polynomial.constantCoeff_apply, h, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij,
        Matrix.one_apply_ne (e.injective.ne (Sum.inl_injective.ne hij))]
  have hmem := hσ σ hdσ hσ0
  rw [← elementaryReindexGroup_map (R := B[X]) e]
  exact Subgroup.mem_map_of_mem _ hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_block_mem

/-- **The reduction**: if `A → A_𝔪` is injective for every maximal `𝔪`, the stabilized
residual at rank `n` gives the normalized block form of R2 at rank `n + 1`. -/
theorem suslinBase3_blockLocal_of_stab {A : Type*} [CommRing A] {n : ℕ}
    (h : SuslinBase3StabLocal A n)
    (hf : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      Function.Injective (algebraMap A (Localization.AtPrime 𝔪))) :
    SuslinR2BlockLocal A (n + 1) := by
  intro τ hdet _ 𝔪 h𝔪 F hF r hblock hnorm
  have hdτ : Matrix.det ((elementaryMatrixUnitMap (ι := Fin (n + 1))
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ :
        (Matrix (Fin (n + 1)) (Fin (n + 1)) (Localization.AtPrime 𝔪)[X])ˣ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (Localization.AtPrime 𝔪)[X]) = 1 := by
    change Matrix.det
      ((Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))).mapMatrix
        (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) A[X])) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hdF := suslin_det_eq_one_of_mem_elementaryGroup hF
  have hdT : Matrix.det ((elementaryMatrixUnitMap (ι := Fin (n + 1))
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ * F :
        (Matrix (Fin (n + 1)) (Fin (n + 1)) (Localization.AtPrime 𝔪)[X])ˣ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (Localization.AtPrime 𝔪)[X]) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdτ, hdF, one_mul]
  have hT := suslinBase3_block_mem (B := Localization.AtPrime 𝔪)
    (fun σ hσ hσ0 ↦ suslinBase3_stab_mem h 𝔪 h𝔪 (hf 𝔪 h𝔪) σ hσ hσ0)
    _ r hblock hdT hnorm
  have hmem := mul_mem hT (inv_mem hF)
  rwa [mul_inv_cancel_right] at hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_blockLocal_of_stab
