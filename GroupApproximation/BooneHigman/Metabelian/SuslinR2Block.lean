import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksStatement
import GroupApproximation.KOne.RankNElimination
import GroupApproximation.Meta.AxiomGuard

/-!
# Stabilizer step (R2), part 1: from a basis row to a normalized coordinate block

Lane `bh-met-90k`.  Matrix bookkeeping for the stabilizer step (R2) of
`SuslinHorrocksSplitLocal` (`SuslinHorrocksStatement.lean`).  Everything here is proved
outright, for every ring.

* `suslinR2_colFactors_apply`: the product of the transvections `x_{k r}(f k)`, `k ≠ r`, used
  as a *right* factor, is the identity with column `r` replaced by `f` (when `f r = 1`).
* `suslinR2_mul_colFactors_mem`: if row `r` of `M ∈ GL_ι(R)` is `e_r`, then right
  multiplication by these transvections with `f = (column r of M⁻¹)` makes column `r` equal to
  `e_r` as well, i.e. lands in `coordinateBlock R r` (`diag(GL_{ι∖r}, 1)`).  Row `r` of `M⁻¹`
  is `e_r`, so `f r = 1`.
* `suslinR2_map_mem_coordinateBlock`: coefficient maps preserve coordinate blocks.
* `suslinR2_block_core`: over `B[X]`, if `T(0) = 1`, `F ∈ E_ι(B[X])` and row `r` of `T F` is
  `e_r`, then some `F' ∈ E_ι(B[X])` makes `T F'` a coordinate block at `r` with `(T F')(0) = 1`.
  The normalization multiplies by the constant matrix `(T F₁)(0)⁻¹ ∈ E_ι(B)`, which is again a
  coordinate block, so the block shape survives.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

section Generic

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- The product of the transvections `x_{k r}(f k)`, `k ≠ r`, is the identity matrix with
column `r` replaced by `f`, provided `f r = 1`. -/
theorem suslinR2_colFactors_apply (r : ι) (f : ι → R) (hfr : f r = 1) (k c : ι) :
    (((leftClearFactors r f (otherIndices r)).prod : (Matrix ι ι R)ˣ) : Matrix ι ι R) k c =
      if c = r then f k else (1 : Matrix ι ι R) k c := by
  have h := leftClearFactors_mul_apply (1 : Matrix ι ι R) r f (otherIndices r)
    (otherIndices_nodup r) k c
  rw [Matrix.mul_one] at h
  rw [h]
  by_cases hk : k = r
  · rw [if_neg (fun hm ↦ (mem_otherIndices_values_iff r k).1 hm hk)]
    by_cases hc : c = r
    · rw [if_pos hc, hk, hc, hfr, Matrix.one_apply_eq]
    · rw [if_neg hc]
  · rw [if_pos ((mem_otherIndices_values_iff r k).2 hk)]
    by_cases hc : c = r
    · rw [if_pos hc, hc, Matrix.one_apply_ne hk, Matrix.one_apply_eq, mul_one, zero_add]
    · rw [if_neg hc, Matrix.one_apply_ne (Ne.symm hc), mul_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_colFactors_apply

/-- **Clearing column `r` by right factors.**  If row `r` of `M` is `e_r` and `M W = 1`, then
right multiplication by the transvections `x_{k r}(W k r)`, `k ≠ r`, gives a coordinate block
at `r`. -/
theorem suslinR2_mul_colFactors_mem (M : (Matrix ι ι R)ˣ) (W : Matrix ι ι R) (r : ι)
    (hMW : (M : Matrix ι ι R) * W = 1)
    (hrow : ∀ c : ι, (M : Matrix ι ι R) r c = if c = r then 1 else 0) :
    M * (leftClearFactors r (fun k ↦ W k r) (otherIndices r)).prod ∈
      coordinateBlock R r := by
  have hWrow : ∀ c : ι, W r c = (1 : Matrix ι ι R) r c := by
    intro c
    rw [← hMW, Matrix.mul_apply, Finset.sum_eq_single r]
    · rw [hrow r, if_pos rfl, one_mul]
    · intro b _ hb
      rw [hrow b, if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ r) h
  have hWrr : W r r = 1 := by rw [hWrow r, Matrix.one_apply_eq]
  obtain ⟨P, hPdef⟩ : ∃ P : (Matrix ι ι R)ˣ,
      (leftClearFactors r (fun k ↦ W k r) (otherIndices r)).prod = P := ⟨_, rfl⟩
  have hP : ∀ k c : ι, (P : Matrix ι ι R) k c =
      if c = r then W k r else (1 : Matrix ι ι R) k c := by
    intro k c
    rw [← hPdef]
    exact suslinR2_colFactors_apply r (fun k ↦ W k r) hWrr k c
  have hMP : ∀ i c : ι, ((M * P : (Matrix ι ι R)ˣ) : Matrix ι ι R) i c =
      if c = r then (1 : Matrix ι ι R) i r else (M : Matrix ι ι R) i c := by
    intro i c
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hc : c = r
    · rw [if_pos hc, ← hMW, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hP x c, if_pos hc]
    · rw [if_neg hc]
      conv_rhs => rw [← Matrix.mul_one (M : Matrix ι ι R)]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hP x c, if_neg hc]
  rw [hPdef]
  constructor
  · intro c
    rw [hMP r c]
    by_cases hc : c = r
    · rw [if_pos hc, if_pos hc.symm, Matrix.one_apply_eq]
    · rw [if_neg hc, if_neg (Ne.symm hc), hrow c, if_neg hc]
  · intro i
    rw [hMP i r, if_pos rfl, Matrix.one_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_mul_colFactors_mem

/-- Coefficient maps preserve coordinate blocks. -/
theorem suslinR2_map_mem_coordinateBlock {S : Type*} [Ring S] (f : R →+* S) {j : ι}
    {A : (Matrix ι ι R)ˣ} (hA : A ∈ coordinateBlock R j) :
    elementaryMatrixUnitMap f A ∈ coordinateBlock S j := by
  have hA' : IsCoordinateBlock j A := hA
  constructor
  · intro c
    change f ((A : Matrix ι ι R) j c) = _
    rw [hA'.1 c]
    split_ifs <;> simp
  · intro i
    change f ((A : Matrix ι ι R) i j) = _
    rw [hA'.2 i]
    split_ifs <;> simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_map_mem_coordinateBlock

end Generic

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
