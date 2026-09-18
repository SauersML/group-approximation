import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndLocal
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import GroupApproximation.PropertyTT.StabilizationCoordinateBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank induction for R2, part 4: the block form at rank `n + 1` from the local case at rank `n`

Lane `bh-met-90q`.  `suslinR2Ind_blockLocal_succ`: suppose `A → A_𝔪` is injective for every
maximal `𝔪`.  Then `SuslinLocalCaseStatement A n` implies `SuslinR2BlockLocal A (n + 1)`.

**Proof.**  Write `T = τ_𝔪 F`, a coordinate block at `r` with `T(0) = 1`.  Then `T` is
`diag(σ, 1)` up to reindexing (`range_reindexedStabilize_eq_coordinateBlock`).  Also
`det σ = det T = 1` and `σ(0) = 1`.  By `suslinR2Ind_mem_of_localCase`, `σ ∈ E_n(A_𝔪[X])`, so
`T ∈ E_{n+1}`, and `τ_𝔪 = T F⁻¹ ∈ E_{n+1}`.

This removes the type mismatch recorded in `SuslinR2Statement.lean`: the block `σ` over
`A_𝔪[X]` is handled by the dilation lift of `SuslinR2IndLift.lean`, so no localization closure
of the family is needed.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The `(inl i, inl j)` entry of a reindexed stabilization is the `(i, j)` entry. -/
theorem suslinR2Ind_reindex_stab_apply {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ⊕ Unit ≃ κ) (u : (Matrix ι ι R)ˣ) (i j : ι) :
    ((elementaryReindexUnitEquiv (R := R) e (stabilizeUnit (R := R) (κ := Unit) u) :
        (Matrix κ κ R)ˣ) : Matrix κ κ R) (e (Sum.inl i)) (e (Sum.inl j)) =
      (u : Matrix ι ι R) i j := by
  change (Matrix.reindexRingEquiv R e) (Matrix.fromBlocks (u : Matrix ι ι R) 0 0 1)
    (e (Sum.inl i)) (e (Sum.inl j)) = _
  rw [Matrix.coe_reindexRingEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_reindex_stab_apply

/-- **Normalized coordinate blocks are elementary** at rank `n + 1`, given that every normalized
`σ ∈ SL_n(B[X])` is elementary. -/
theorem suslinR2Ind_block_mem {B : Type*} [CommRing B] {n : ℕ}
    (hσ : ∀ σ : (Matrix (Fin n) (Fin n) B[X])ˣ,
      Matrix.det (σ : Matrix (Fin n) (Fin n) B[X]) = 1 →
        elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) σ = 1 →
          σ ∈ elementaryGroup (Fin n) B[X])
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
  have hmem : stabilizeUnit (R := B[X]) (κ := Unit) σ ∈ elementaryGroup (Fin n ⊕ Unit) B[X] :=
    (elementaryStabilization (κ := Unit) ⟨σ, hσ σ hdσ hσ0⟩).2
  rw [← elementaryReindexGroup_map (R := B[X]) e]
  exact Subgroup.mem_map_of_mem _ hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_block_mem

/-- **One rank up**: if `A → A_𝔪` is injective for every maximal `𝔪`, the local case at rank `n`
gives the normalized block form of R2 at rank `n + 1`. -/
theorem suslinR2Ind_blockLocal_succ {A : Type*} [CommRing A] {n : ℕ}
    (hL : SuslinLocalCaseStatement A n)
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
  have hT := suslinR2Ind_block_mem
    (fun σ hσ hσ0 ↦ suslinR2Ind_mem_of_localCase hL 𝔪 h𝔪 (hf 𝔪 h𝔪) σ hσ hσ0)
    _ r hblock hdT hnorm
  have hmem := mul_mem hT (inv_mem hF)
  rwa [mul_inv_cancel_right] at hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_blockLocal_succ

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
