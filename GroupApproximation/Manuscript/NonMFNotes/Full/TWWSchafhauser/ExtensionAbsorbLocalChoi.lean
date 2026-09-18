import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosFiniteDim

/-!
# Choi expansion of completely positive maps out of finite-dimensional algebras

Lane `TWWSch3c2C2`, work order `WO-TWWSch-3c2-C2`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), absorption step. Sources: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6; M.-D. Choi, *Completely positive
linear maps on complex matrices*, Linear Algebra Appl. 10 (1975), Thm. 2.

`exists_choi_expansion`: a completely positive `β : D → S` out of a nontrivial
finite-dimensional C*-algebra has the form `β(d) = ∑ᵢⱼ e(d)ᵢⱼ ∑ₗ Pₗᵢ⋆ Pₗⱼ` for a matrix picture
`e : D →⋆ₐ M_k(ℂ)` (the unital cp retract `D → M_k → D`) and a factorization `P⋆P` of the Choi
matrix of `β ∘ retract`.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance absorbLocalChoiMatrixCStarAlgebra (Z : Type*) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable {S : Type} [CStarAlgebra S]

/-- **Choi expansion.** A completely positive `β : D → S` out of a nontrivial
finite-dimensional C*-algebra is `β(d) = ∑ᵢ ∑ⱼ e(d)ᵢⱼ ∑ₗ Pₗᵢ⋆ Pₗⱼ` for a unital `⋆`-embedding
`e : D → M_k(ℂ)` and some `P` (Choi 1975, Thm. 2; Elliott--Kucerovsky 2001, proof of Thm. 6;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem exists_choi_expansion (D : FinDimCStarAlgebra) [Nontrivial D] (β : D →ₗ[ℂ] S)
    (hβ : IsCompletelyPositive β) :
    ∃ (k : ℕ) (e : D →⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) (P : Fin k → Fin k → S),
      ∀ d : D, β d = ∑ i, ∑ j, e d i j • ∑ l, star (P l i) * P l j := by
  obtain ⟨R⟩ := BlackadarKirchberg.exists_matrixUCPRetract_of_finiteDimensionalCStar D
  obtain ⟨k, ⟨ε⟩⟩ : ∃ k : ℕ, Nonempty (R.model ≃ Fin k) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  haveI : Nonempty (Fin k) := ⟨ε (Classical.arbitrary R.model)⟩
  let ρ : Matrix R.model R.model ℂ ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    choiEffrosMatrixReindex ε
  let f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] S :=
    β ∘ₗ R.retract ∘ₗ (ρ.symm.toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix R.model R.model ℂ)
  have hf : IsCompletelyPositive f :=
    hβ.comp (R.retract_completelyPositive.comp
      (isCompletelyPositive_of_starAlgHom ρ.symm.toStarAlgHom.toNonUnitalStarAlgHom))
  obtain ⟨P, hP⟩ := BlackadarKirchberg.exists_factor_choiMatrix_of_cp f hf
  let e : D →⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ := ρ.toStarAlgHom.comp R.embedding
  refine ⟨k, e, fun l i => P l i, fun d => ?_⟩
  have hentry : ∀ i j : Fin k, f (Matrix.single i j 1) = ∑ l, star (P l i) * P l j := by
    intro i j
    have h : BlackadarKirchberg.choiMatrix f i j = (star P * P) i j := by rw [hP]
    rw [BlackadarKirchberg.choiMatrix_apply, cstarMatrix_mul_apply] at h
    rw [h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cstarMatrix_star_apply]
  have hfe : f (e d) = β d := by
    change β (R.retract (ρ.symm (ρ (R.embedding d)))) = β d
    rw [StarAlgEquiv.symm_apply_apply, R.retract_embedding]
  calc β d = f (e d) := hfe.symm
    _ = f (∑ i : Fin k, ∑ j : Fin k, e d i j • Matrix.single i j 1) :=
        congrArg f (BlackadarKirchberg.matrix_eq_sum_smul_single (e d))
    _ = ∑ i, ∑ j, e d i j • ∑ l, star (P l i) * P l j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hentry]

end

end GroupApproximation.Full.TWWSchafhauser
