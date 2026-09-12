import GroupApproximation.GroupTheory.HigmanThompson.CompactConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite truncations of Brown's conjugacy

`compE m r` has infinitely many breakpoints (they accumulate at `r`), so it is not uniformly
grid-affine.  Any element of `F_{n,∞}` or `F_{n,r}` only sees finitely many blocks before
it becomes a translation or an affine germ, so it suffices to replace `compE` beyond the
block `r - 1 + J` by a translation (`compET m r J`).  The truncation is a strictly increasing
bijection of `ℚ` (`compET_strictMono`, inverse `compEinvT`), agrees with `compE` up to
`r - 1 + J`, and is uniformly grid-affine (`compET_gridAffine`), as is its inverse
(`compEinvT_gridAffine`).
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m r : ℕ)

theorem AffineOn.slope_unique {f : ℚ → ℚ} {a b s s' : ℚ} (h : AffineOn f a b s)
    (h' : AffineOn f a b s') (hab : a < b) : s = s' := by
  have h1 := h b hab.le le_rfl
  have h2 := h' b hab.le le_rfl
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have h3 : s * (b - a) = s' * (b - a) := by linarith
  exact mul_right_cancel₀ hne h3

/-- **`compE` on the integer block `[r-1+j, r+j]`.** -/
theorem compE_affine_block (j : ℕ) :
    AffineOn (compE m r) ((r : ℚ) - 1 + j) ((r : ℚ) - 1 + j + 1)
      ((((m : ℚ) + 2) ^ (j / (m + 1) + 1))⁻¹) := by
  have hdm := Nat.div_add_mod j (m + 1)
  have hρlt := Nat.mod_lt j (show 0 < m + 1 by omega)
  have hj : (j : ℚ) = ((j / (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) + ((j % (m + 1) : ℕ) : ℚ) := by
    have hc : (((m + 1) * (j / (m + 1)) + j % (m + 1) : ℕ) : ℚ) = (j : ℚ) := by
      exact_mod_cast hdm
    push_cast at hc
    linarith
  have hρ0 : (0 : ℚ) ≤ ((j % (m + 1) : ℕ) : ℚ) := Nat.cast_nonneg _
  have hρm : ((j % (m + 1) : ℕ) : ℚ) ≤ (m : ℚ) := by
    have h : j % (m + 1) ≤ m := by omega
    exact_mod_cast h
  intro x hx1 hx2
  have hw0 : 0 ≤ ((j % (m + 1) : ℕ) : ℚ) + (x - ((r : ℚ) - 1 + j)) := by linarith
  have hw1 : ((j % (m + 1) : ℕ) : ℚ) + (x - ((r : ℚ) - 1 + j)) ≤ (m : ℚ) + 1 := by linarith
  have e1 : x = (r : ℚ) - 1 + ((j / (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) +
      (((j % (m + 1) : ℕ) : ℚ) + (x - ((r : ℚ) - 1 + j))) := by
    rw [hj]
    ring
  have e2 : (r : ℚ) - 1 + j = (r : ℚ) - 1 + ((j / (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) +
      ((j % (m + 1) : ℕ) : ℚ) := by
    rw [hj]
    ring
  have hx := compE_block m r (j / (m + 1)) hw0 hw1
  have h0 := compE_block m r (j / (m + 1)) hρ0 (by linarith)
  rw [← e1] at hx
  rw [← e2] at h0
  rw [hx, h0]
  ring

theorem compE_block_mem (j : ℕ) : compE m r ((r : ℚ) - 1 + j) ∈ Grid (m + 2) (j / (m + 1) + 1) := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have h := compE_affine_block m r j ((r : ℚ) - 1 + j) le_rfl (by linarith)
  have hdm := Nat.div_add_mod j (m + 1)
  have hρlt := Nat.mod_lt j (show 0 < m + 1 by omega)
  have hj : (j : ℚ) = ((j / (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) + ((j % (m + 1) : ℕ) : ℚ) := by
    have hc : (((m + 1) * (j / (m + 1)) + j % (m + 1) : ℕ) : ℚ) = (j : ℚ) := by
      exact_mod_cast hdm
    push_cast at hc
    linarith
  have hρ0 : (0 : ℚ) ≤ ((j % (m + 1) : ℕ) : ℚ) := Nat.cast_nonneg _
  have hρm : ((j % (m + 1) : ℕ) : ℚ) ≤ (m : ℚ) + 1 := by
    have h' : j % (m + 1) ≤ m + 1 := by omega
    exact_mod_cast h'
  have e2 : (r : ℚ) - 1 + j = (r : ℚ) - 1 + ((j / (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) +
      ((j % (m + 1) : ℕ) : ℚ) := by
    rw [hj]
    ring
  rw [e2, compE_block m r (j / (m + 1)) hρ0 hρm]
  refine ⟨(r : ℤ) * ((m : ℤ) + 2) ^ (j / (m + 1) + 1) - ((m : ℤ) + 2) + (j % (m + 1) : ℕ), ?_⟩
  have hcastn : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  rw [hcastn]
  have e3 : (((m : ℚ) + 2) ^ (j / (m + 1)))⁻¹ * ((m : ℚ) + 2) ^ (j / (m + 1) + 1) = (m : ℚ) + 2 := by
    rw [pow_succ]
    field_simp
  have e4 : (((m : ℚ) + 2) ^ (j / (m + 1) + 1))⁻¹ * ((m : ℚ) + 2) ^ (j / (m + 1) + 1) = 1 :=
    inv_mul_cancel₀ (pow_pos hp _).ne'
  push_cast
  linear_combination (-1 : ℚ) * e3 + ((j % (m + 1) : ℕ) : ℚ) * e4

/-- The truncation of `compE` beyond `r - 1 + J`. -/
noncomputable def compET (J : ℕ) (u : ℚ) : ℚ :=
  if u ≤ (r : ℚ) - 1 + J then compE m r u else
    compE m r ((r : ℚ) - 1 + J) + (u - ((r : ℚ) - 1 + J))

theorem compET_of_le {J : ℕ} {u : ℚ} (h : u ≤ (r : ℚ) - 1 + J) : compET m r J u = compE m r u := by
  simp [compET, h]

theorem compET_of_ge {J : ℕ} {u : ℚ} (h : (r : ℚ) - 1 + J ≤ u) :
    compET m r J u = compE m r ((r : ℚ) - 1 + J) + (u - ((r : ℚ) - 1 + J)) := by
  unfold compET
  split_ifs with h'
  · have hu : u = (r : ℚ) - 1 + J := le_antisymm h' h
    rw [hu]
    ring
  · rfl

theorem compET_strictMono (J : ℕ) : StrictMono (compET m r J) := by
  intro u u' huu'
  rcases le_or_lt u' ((r : ℚ) - 1 + J) with h' | h'
  · rw [compET_of_le m r h', compET_of_le m r (le_trans huu'.le h')]
    exact compE_strictMono m r huu'
  rcases le_or_lt u ((r : ℚ) - 1 + J) with h | h
  · rw [compET_of_le m r h, compET_of_ge m r h'.le]
    have h1 := (compE_strictMono m r).monotone h
    linarith
  · rw [compET_of_ge m r h.le, compET_of_ge m r h'.le]
    linarith

/-- The inverse of the truncation. -/
noncomputable def compEinvT (J : ℕ) (t : ℚ) : ℚ :=
  if t ≤ compE m r ((r : ℚ) - 1 + J) then compEinv m r t else
    (r : ℚ) - 1 + J + (t - compE m r ((r : ℚ) - 1 + J))

theorem compEinvT_compET (J : ℕ) (u : ℚ) : compEinvT m r J (compET m r J u) = u := by
  rcases le_or_lt u ((r : ℚ) - 1 + J) with h | h
  · rw [compET_of_le m r h]
    have hle : compE m r u ≤ compE m r ((r : ℚ) - 1 + J) := (compE_strictMono m r).monotone h
    simp only [compEinvT, if_pos hle]
    exact compEinv_compE m r u
  · rw [compET_of_ge m r h.le]
    have hgt : ¬ (compE m r ((r : ℚ) - 1 + J) + (u - ((r : ℚ) - 1 + J)) ≤
        compE m r ((r : ℚ) - 1 + J)) := by
      intro hc
      linarith
    simp only [compEinvT, if_neg hgt]
    ring

theorem compET_compEinvT (J : ℕ) (t : ℚ) : compET m r J (compEinvT m r J t) = t := by
  rcases le_or_lt t (compE m r ((r : ℚ) - 1 + J)) with h | h
  · simp only [compEinvT, if_pos h]
    have ht : t < r := lt_of_le_of_lt h (compE_lt m r _)
    have hle : compEinv m r t ≤ (r : ℚ) - 1 + J := by
      by_contra hc
      have hc' := compE_strictMono m r (not_le.mp hc)
      rw [compE_compEinv m r ht] at hc'
      linarith
    rw [compET_of_le m r hle, compE_compEinv m r ht]
  · simp only [compEinvT, if_neg (not_le.mpr h)]
    rw [compET_of_ge m r (by linarith)]
    ring

#audit_axioms GroupApproximation.HigmanThompson.compE_affine_block
#audit_axioms GroupApproximation.HigmanThompson.compET_strictMono

end HigmanThompson
end GroupApproximation
