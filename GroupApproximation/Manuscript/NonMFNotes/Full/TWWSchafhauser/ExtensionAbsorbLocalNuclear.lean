import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbLocalMatrix
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbLocalChoi

/-!
# Nuclear reduction of the local compression

Lane `TWWSch3c2C2`, work order `WO-TWWSch-3c2-C2`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), absorption step. Source: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6 (a nuclear map into the compacts is
a point-norm limit of maps factoring through finite-dimensional algebras).

* `isLocallyCompressible_nuclear_block`: for completely positive `α : S → D`, `β : D → S` with
  `D` finite-dimensional, `s ↦ k⋆ σ(β(α s)) k` is a finite sum of matrix blocks
  `matrixBlockMap (e ∘ α) b` with `bᵢ = σ(Pₗᵢ) k` compact (Choi expansion of `β`), hence is
  compressible into a matrix-compressible lift.
* `IsMatrixCompressible.conj_of_nuclear`: for nuclear `S`, a contractive `⋆`-homomorphism
  `σ : S → 𝓑(H_J)` and compact `k`, `s ↦ k⋆ σ(s) k` is locally compressible into every
  matrix-compressible lift (approximate `id_S` by `β ∘ α`).

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule GroupApproximation.CStarExactness

noncomputable section

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Reordering a triple finite sum (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem absorbLocal_sum_comm_three {κ Y : Type} [Fintype κ] [Fintype Y]
    (F : κ → Y → Y → StdBdd J) :
    ∑ l, ∑ i, ∑ j, F l i j = ∑ i, ∑ j, ∑ l, F l i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- A map `s ↦ k⋆ σ(β(α s)) k` through a finite-dimensional algebra is compressible into a
matrix-compressible lift (Elliott--Kucerovsky 2001, proof of Thm. 6;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem isLocallyCompressible_nuclear_block {ℓ : S → StdBdd J} (hℓ : IsMatrixCompressible ℓ)
    (D : FinDimCStarAlgebra) (α : S →ₗ[ℂ] D) (hα : IsCompletelyPositive α) (β : D →ₗ[ℂ] S)
    (hβ : IsCompletelyPositive β) (σ : S →⋆ₐ[ℂ] StdBdd J) (k : StdBdd J)
    (hk : IsStdCompact k) :
    IsLocallyCompressible ℓ (fun s => star k * σ (β (α s)) * k) := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · have key : (fun s => star k * σ (β (α s)) * k) = fun _ => (0 : StdBdd J) := by
      funext s
      rw [Subsingleton.elim (α s) 0, map_zero, map_zero, mul_zero, zero_mul]
    rw [key]
    exact isLocallyCompressible_zero
  · obtain ⟨n, e, P, hP⟩ := exists_choi_expansion D β hβ
    have key : (fun s => star k * σ (β (α s)) * k) = fun s =>
        ∑ l ∈ Finset.univ, matrixBlockMap (fun s => e (α s)) (fun i => σ (P l i) * k) s := by
      funext s
      simp only [matrixBlockMap]
      rw [hP (α s)]
      simp only [map_sum, map_smul, map_mul, map_star, Finset.mul_sum, Finset.sum_mul,
        mul_smul_comm, smul_mul_assoc, Finset.smul_sum, star_mul, mul_assoc]
      exact (absorbLocal_sum_comm_three _).symm
    rw [key]
    exact hℓ.sum D α hα e Finset.univ (fun l i => σ (P l i) * k)
      fun l _ i => hk.mul_left (σ (P l i))

/-- **Nuclear reduction.** If `S` is nuclear, `σ : S → 𝓑(H_J)` is a contractive
`⋆`-homomorphism and `k` is compact, then `s ↦ k⋆ σ(s) k` is locally compressible into every
matrix-compressible lift `ℓ` (Elliott--Kucerovsky 2001, proof of Thm. 6;
`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsMatrixCompressible.conj_of_nuclear {ℓ : S → StdBdd J} (hℓ : IsMatrixCompressible ℓ)
    (hS : IsNuclearCStarAlgebra S) (σ : S →⋆ₐ[ℂ] StdBdd J) (hσ : ∀ s, ‖σ s‖ ≤ ‖s‖)
    (k : StdBdd J) (hk : IsStdCompact k) :
    IsLocallyCompressible ℓ (fun s => star k * σ s * k) := by
  refine isLocallyCompressible_of_approx fun G ε hε => ?_
  have hM : 0 < ‖k‖ ^ 2 + 1 := by positivity
  have hδ : 0 < ε / (‖k‖ ^ 2 + 1) := div_pos hε hM
  have hδM : ε / (‖k‖ ^ 2 + 1) * (‖k‖ ^ 2 + 1) = ε := div_mul_cancel₀ ε hM.ne'
  obtain ⟨D, α, β, hα, hβ, -, -, hαβ⟩ := hS G (ε / (‖k‖ ^ 2 + 1)) hδ
  refine ⟨fun s => star k * σ (β (α s)) * k,
    isLocallyCompressible_nuclear_block hℓ D α hα β hβ σ k hk, fun s hs => ?_⟩
  show ‖star k * σ (β (α s)) * k - star k * σ s * k‖ ≤ ε
  have h1 : ‖β (α s) - s‖ ≤ ε / (‖k‖ ^ 2 + 1) := by
    have h := hαβ s hs
    rwa [LinearMap.id_apply] at h
  have h2 : ‖σ (β (α s) - s)‖ ≤ ε / (‖k‖ ^ 2 + 1) := (hσ _).trans h1
  have e : star k * σ (β (α s)) * k - star k * σ s * k = star k * σ (β (α s) - s) * k := by
    rw [map_sub, mul_sub, sub_mul]
  have h3 : ‖star k * σ (β (α s) - s) * k‖ ≤ ‖k‖ * (ε / (‖k‖ ^ 2 + 1)) * ‖k‖ := by
    calc ‖star k * σ (β (α s) - s) * k‖ ≤ ‖star k‖ * ‖σ (β (α s) - s)‖ * ‖k‖ := norm_mul₃_le
      _ ≤ ‖k‖ * (ε / (‖k‖ ^ 2 + 1)) * ‖k‖ := by
          rw [norm_star]
          gcongr
  rw [e]
  nlinarith [h3, hδM, hδ, norm_nonneg k]

end

end GroupApproximation.Full.TWWSchafhauser
