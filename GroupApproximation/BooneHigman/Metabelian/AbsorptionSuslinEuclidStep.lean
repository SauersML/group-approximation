import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import Mathlib.LinearAlgebra.Matrix.Transvection
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin input, part 3: `SL_N = E_N` over a ring with well-founded division

Lane `bh-met-23`.  With the Euclidean planting step `suslin_exists_diag_one` of
`AbsorptionSuslinEuclidKill.lean` in place of `RankNElimination.exists_diag_one`, the clearing
step and the iteration of `KOne/RankNElimination.lean` go through verbatim (they only use the
pivot `1`), giving `E · A · F = diagAt l u` for every invertible `A`
(`suslin_exists_elementary_mul_diagAt`).  Determinants of elementary matrices are `1` over any
commutative ring, and `det (diagAt l u) = u`, so a determinant-one matrix is elementary:
`specialLinearInElementary_of_hasWellFoundedDivision`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **One more index clears** (Euclidean version of `RankNElimination.exists_clear_step`). -/
theorem suslin_exists_clear_step (hR : HasWellFoundedDivision R)
    (A : (Matrix ι ι R)ˣ) (S : Finset ι) (hA : ClearedOn S A)
    (k t : ι) (hk : k ∉ S) (ht : t ∉ S) (hkt : k ≠ t) :
    ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn (insert t S) M := by
  obtain ⟨C, hCr, hCcl, hCtt⟩ := suslin_exists_diag_one hR A S hA k t hk ht hkt
  have hCcoef : ∀ j ∈ S, -(C : Matrix ι ι R) t j = 0 := by
    intro j hj
    rw [hCcl.col hj t, if_neg (fun h : t = j ↦ ht (h ▸ hj)), neg_zero]
  obtain ⟨D, hDr, hDcl, hDrow⟩ :
      ∃ D : (Matrix ι ι R)ˣ, Reaches C D ∧ ClearedOn S D ∧
        ∀ c : ι, (D : Matrix ι ι R) t c = if t = c then 1 else 0 := by
    refine ⟨C * (rightClearFactors t (fun c ↦ -(C : Matrix ι ι R) t c)
        (otherIndices t)).prod,
      Reaches.right (rightClearFactors_prod_mem t _),
      hCcl.mul (rightClearFactors_clearedOn S ht _ hCcoef), fun c ↦ ?_⟩
    rw [Units.val_mul]
    exact rightClearFactors_clear_row (C : Matrix ι ι R) t hCtt c
  have hDcoef : ∀ j ∈ S, -(D : Matrix ι ι R) j t = 0 := by
    intro j hj
    rw [hDcl.row hj t, if_neg (fun h : j = t ↦ ht (h ▸ hj)), neg_zero]
  refine ⟨(leftClearFactors t (fun r ↦ -(D : Matrix ι ι R) r t)
      (otherIndices t)).prod * D,
    hCr.trans (hDr.trans (Reaches.left (leftClearFactors_prod_mem t _))), ?_⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hjS
  · exact leftClearFactors_make_coordinateBlock D j hDrow
  · exact mul_mem
      ((leftClearFactors_clearedOn S ht _ hDcoef) j hjS) (hDcl j hjS)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_clear_step

/-- Clearing every index other than `l`, one index at a time, always pivoting on `l`
(Euclidean version of `RankNElimination.exists_cleared_erase`). -/
theorem suslin_exists_cleared_erase (hR : HasWellFoundedDivision R) (l : ι) :
    ∀ (n : ℕ) (S : Finset ι) (A : (Matrix ι ι R)ˣ), l ∉ S →
      (Finset.univ.erase l \ S).card = n → ClearedOn S A →
      ∃ M : (Matrix ι ι R)ˣ, Reaches A M ∧ ClearedOn (Finset.univ.erase l) M := by
  intro n
  induction n with
  | zero =>
      intro S A _ hcard hA
      exact ⟨A, Reaches.refl A, hA.mono
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard))⟩
  | succ n IH =>
      intro S A hlS hcard hA
      have hne : (Finset.univ.erase l \ S).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨m, hm⟩ := hne
      have hmS : m ∉ S := (Finset.mem_sdiff.mp hm).2
      have hml : m ≠ l := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hm).1).1
      obtain ⟨M, hMr, hM⟩ :=
        suslin_exists_clear_step hR A S hA l m hlS hmS (Ne.symm hml)
      have hset : Finset.univ.erase l \ insert m S =
          (Finset.univ.erase l \ S).erase m := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_univ, and_true, not_or]
        tauto
      have hcard' : (Finset.univ.erase l \ insert m S).card = n := by
        rw [hset, Finset.card_erase_of_mem hm, hcard]
        omega
      have hlS' : l ∉ insert m S := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h ↦ hml h.symm, hlS⟩
      obtain ⟨N, hNr, hN⟩ := IH (insert m S) M hlS' hcard' hM
      exact ⟨N, hMr.trans hNr, hN⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_exists_cleared_erase

/-- **Euclidean elimination at every rank**: `A = E · diagAt l u · F` with `E, F` elementary. -/
theorem suslin_eq_elementary_mul_diagAt (hR : HasWellFoundedDivision R)
    (A : (Matrix ι ι R)ˣ) (l : ι) :
    ∃ E ∈ elementaryGroup ι R, ∃ F ∈ elementaryGroup ι R, ∃ u : Rˣ,
      A = E * diagAt l u * F := by
  obtain ⟨M, hMr, hM⟩ := suslin_exists_cleared_erase hR l
    (Finset.univ.erase l \ (∅ : Finset ι)).card ∅ A
    (Finset.notMem_empty l) rfl (clearedOn_empty _)
  obtain ⟨u, hu⟩ := exists_eq_diagAt hM
  obtain ⟨E, hE, F, hF, hEF⟩ := hMr
  refine ⟨E⁻¹, inv_mem hE, F⁻¹, inv_mem hF, u, ?_⟩
  rw [← hu, hEF]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_eq_elementary_mul_diagAt

/-- Over a commutative ring, elementary matrices have determinant `1`. -/
theorem suslin_det_eq_one_of_mem_elementaryGroup {u : (Matrix ι ι R)ˣ}
    (hu : u ∈ elementaryGroup ι R) : Matrix.det (u : Matrix ι ι R) = 1 := by
  have hle : elementaryGroup ι R ≤
      (Units.map (Matrix.detMonoidHom : Matrix ι ι R →* R)).ker := by
    rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    show Matrix.det (Matrix.transvection i j a) = ((1 : Rˣ) : R)
    rw [Matrix.det_transvection_of_ne i j hij a, Units.val_one]
  exact congrArg Units.val (MonoidHom.mem_ker.mp (hle hu))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_det_eq_one_of_mem_elementaryGroup

/-- The determinant of `diagAt l u` is `u`. -/
theorem suslin_det_diagAt (l : ι) (u : Rˣ) :
    Matrix.det ((diagAt l u : (Matrix ι ι R)ˣ) : Matrix ι ι R) = u := by
  rw [diagAt_val, Matrix.det_diagonal]
  simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_det_diagAt

/-- `diagAt l 1 = 1`. -/
theorem suslin_diagAt_one (l : ι) : diagAt l (1 : Rˣ) = 1 := by
  apply Units.ext
  have hfun : (fun i : ι ↦ if i = l then ((1 : Rˣ) : R) else 1) = fun _ ↦ (1 : R) := by
    funext i
    by_cases h : i = l <;> simp [h]
  rw [diagAt_val, hfun]
  exact Matrix.diagonal_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslin_diagAt_one

/-- **`SL_N = E_N` over a ring with well-founded division**, at every positive rank. -/
theorem specialLinearInElementary_of_hasWellFoundedDivision (hR : HasWellFoundedDivision R)
    {N : ℕ} (hN : 0 < N) : SpecialLinearInElementary R N := by
  intro u hu
  obtain ⟨E, hE, F, hF, v, huv⟩ := suslin_eq_elementary_mul_diagAt hR u (⟨0, hN⟩ : Fin N)
  have hd : Matrix.det (u : Matrix (Fin N) (Fin N) R) =
      Matrix.det ((E * diagAt (⟨0, hN⟩ : Fin N) v * F : (Matrix (Fin N) (Fin N) R)ˣ) :
        Matrix (Fin N) (Fin N) R) := by
    rw [← huv]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
    suslin_det_eq_one_of_mem_elementaryGroup hE, suslin_det_eq_one_of_mem_elementaryGroup hF,
    suslin_det_diagAt, one_mul, mul_one, hu] at hd
  have hv : v = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact hd.symm
  rw [huv, hv, suslin_diagAt_one, mul_one]
  exact mul_mem hE hF

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_of_hasWellFoundedDivision

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
