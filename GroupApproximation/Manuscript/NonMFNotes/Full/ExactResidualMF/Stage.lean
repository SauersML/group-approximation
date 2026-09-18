import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidualMF.Gluing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Layered potentials and word balls

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`, and
Shulman (arXiv:2603.13564), proof of Theorem 10.  The rotation of the second
copy of `G` is turned on gradually: on a finite set with layers
`A 0, A 1, …, A (L-1)`, the angle at `w` is `(π/2) · #{k < L | w ∈ A k} / L`.
A map moving every layer into the next one changes the angle by at most
`(π/2)/L`; points in every layer have angle `π/2`, and the rotation is the
identity off the layers.

This file proves those facts (`potCount`, `potAngle`) and introduces the word
balls `dblBall` of the symmetric double that provide the layers.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation

noncomputable section

/-! ## Layer counts -/

section Potential

variable {Y : Type*}

theorem ite_one_zero_le_ite {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then (1 : ℝ) else 0) ≤ if q then 1 else 0 := by
  by_cases hp : p
  · exact le_of_eq (by rw [if_pos hp, if_pos (h hp)])
  · rw [if_neg hp]
    exact ite_nonneg zero_le_one (le_refl 0)

variable (A : ℕ → Set Y) (L : ℕ)

open Classical in
/-- The number of layers `A 0, …, A (L-1)` containing `w`. -/
def potCount (w : Y) : ℝ :=
  ∑ k ∈ Finset.range L, if w ∈ A k then (1 : ℝ) else 0

theorem potCount_zero (w : Y) : potCount A 0 w = 0 :=
  Finset.sum_range_zero _

open Classical in
theorem potCount_succ (w : Y) :
    potCount A (L + 1) w = potCount A L w + if w ∈ A L then (1 : ℝ) else 0 :=
  Finset.sum_range_succ _ L

open Classical in
/-- Moving every layer into the next one loses at most one layer. -/
theorem potCount_shift_le (w w' : Y) (h : ∀ k, k < L → w ∈ A k → w' ∈ A (k + 1)) :
    potCount A L w ≤ potCount A L w' + 1 := by
  have h1 : potCount A L w ≤
      ∑ k ∈ Finset.range L, if w' ∈ A (k + 1) then (1 : ℝ) else 0 := by
    unfold potCount
    exact Finset.sum_le_sum fun k hk => ite_one_zero_le_ite (h k (Finset.mem_range.mp hk))
  have h2 : (∑ k ∈ Finset.range L, if w' ∈ A (k + 1) then (1 : ℝ) else 0) +
      (if w' ∈ A 0 then (1 : ℝ) else 0) =
        potCount A L w' + if w' ∈ A L then (1 : ℝ) else 0 :=
    (Finset.sum_range_succ' (fun k => if w' ∈ A k then (1 : ℝ) else 0) L).symm.trans
      (potCount_succ A L w')
  have h3 : (0 : ℝ) ≤ if w' ∈ A 0 then (1 : ℝ) else 0 := ite_nonneg zero_le_one (le_refl 0)
  have h4 : (if w' ∈ A L then (1 : ℝ) else 0) ≤ 1 := ite_le_one (le_refl 1) zero_le_one
  linarith

theorem abs_potCount_sub_le (w w' : Y) (h : ∀ k, k < L → w ∈ A k → w' ∈ A (k + 1))
    (h' : ∀ k, k < L → w' ∈ A k → w ∈ A (k + 1)) :
    |potCount A L w - potCount A L w'| ≤ 1 := by
  have hww' := potCount_shift_le A L w w' h
  have hw'w := potCount_shift_le A L w' w h'
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem potCount_eq_of_forall (w : Y) (h : ∀ k, k < L → w ∈ A k) : potCount A L w = L := by
  induction L with
  | zero => exact (potCount_zero A w).trans Nat.cast_zero.symm
  | succ L ih =>
    rw [potCount_succ, ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_add_one L))),
      if_pos (h L (Nat.lt_add_one L)), Nat.cast_succ]

theorem exists_mem_of_potCount_ne_zero (w : Y) (h : potCount A L w ≠ 0) :
    ∃ k, k < L ∧ w ∈ A k := by
  by_contra hne
  apply h
  unfold potCount
  exact Finset.sum_eq_zero fun k hk => if_neg fun hw => hne ⟨k, Finset.mem_range.mp hk, hw⟩

/-! ## Angles -/

/-- The rotation angle `(π/2) · potCount / L`. -/
def potAngle (w : Y) : ℝ := Real.pi / 2 / L * potCount A L w

theorem cos_mul_cos_add_sin_mul_sin (w : Y) :
    Real.cos (potAngle A L w) * Real.cos (potAngle A L w) +
      Real.sin (potAngle A L w) * Real.sin (potAngle A L w) = 1 := by
  have h := Real.cos_sq_add_sin_sq (potAngle A L w)
  rw [pow_two, pow_two] at h
  exact h

theorem potAngle_bound_nonneg : 0 ≤ Real.pi / 2 / (L : ℝ) :=
  div_nonneg (div_nonneg Real.pi_pos.le zero_le_two) (Nat.cast_nonneg L)

theorem abs_potAngle_sub_le (w w' : Y) (h : ∀ k, k < L → w ∈ A k → w' ∈ A (k + 1))
    (h' : ∀ k, k < L → w' ∈ A k → w ∈ A (k + 1)) :
    |potAngle A L w - potAngle A L w'| ≤ Real.pi / 2 / L := by
  have hη := potAngle_bound_nonneg L
  unfold potAngle
  rw [← mul_sub, abs_mul, abs_of_nonneg hη]
  exact mul_le_of_le_one_right hη (abs_potCount_sub_le A L w w' h h')

theorem abs_cos_potAngle_sub_le (w w' : Y) (h : ∀ k, k < L → w ∈ A k → w' ∈ A (k + 1))
    (h' : ∀ k, k < L → w' ∈ A k → w ∈ A (k + 1)) :
    |Real.cos (potAngle A L w) - Real.cos (potAngle A L w')| ≤ Real.pi / 2 / L :=
  (Real.abs_cos_sub_cos_le _ _).trans (abs_potAngle_sub_le A L w w' h h')

theorem abs_sin_potAngle_sub_le (w w' : Y) (h : ∀ k, k < L → w ∈ A k → w' ∈ A (k + 1))
    (h' : ∀ k, k < L → w' ∈ A k → w ∈ A (k + 1)) :
    |Real.sin (potAngle A L w) - Real.sin (potAngle A L w')| ≤ Real.pi / 2 / L :=
  (Real.abs_sin_sub_sin_le _ _).trans (abs_potAngle_sub_le A L w w' h h')

theorem potAngle_eq_of_forall (hL : L ≠ 0) (w : Y) (h : ∀ k, k < L → w ∈ A k) :
    potAngle A L w = Real.pi / 2 := by
  unfold potAngle
  rw [potCount_eq_of_forall A L w h]
  exact div_mul_cancel₀ (Real.pi / 2) (Nat.cast_ne_zero.mpr hL)

theorem cos_potAngle_of_forall (hL : L ≠ 0) (w : Y) (h : ∀ k, k < L → w ∈ A k) :
    Real.cos (potAngle A L w) = 0 := by
  rw [potAngle_eq_of_forall A L hL w h, Real.cos_pi_div_two]

theorem sin_potAngle_of_forall (hL : L ≠ 0) (w : Y) (h : ∀ k, k < L → w ∈ A k) :
    Real.sin (potAngle A L w) = 1 := by
  rw [potAngle_eq_of_forall A L hL w h, Real.sin_pi_div_two]

/-- The rotation is supported on the layers. -/
theorem exists_mem_of_sin_potAngle_ne_zero (w : Y) (h : Real.sin (potAngle A L w) ≠ 0) :
    ∃ k, k < L ∧ w ∈ A k := by
  refine exists_mem_of_potCount_ne_zero A L w fun h0 => h ?_
  unfold potAngle
  rw [h0, mul_zero, Real.sin_zero]

end Potential

/-! ## Word balls of the symmetric double -/

section Balls

variable (G : Type) [Group G] (Γ : Subgroup G)

open Classical in
/-- Products of at most `r` letters `inDouble b g` with `g ∈ S`. -/
def dblBall (S : Finset G) : ℕ → Finset (SymmetricDouble G Γ)
  | 0 => {1}
  | r + 1 => dblBall S r ∪
      ((Finset.univ ×ˢ S) ×ˢ dblBall S r).image fun q => inDouble G Γ q.1.1 q.1.2 * q.2

theorem dblBall_zero (S : Finset G) : dblBall G Γ S 0 = {1} := rfl

open Classical in
theorem dblBall_succ (S : Finset G) (r : ℕ) :
    dblBall G Γ S (r + 1) = dblBall G Γ S r ∪
      ((Finset.univ ×ˢ S) ×ˢ dblBall G Γ S r).image
        fun q => inDouble G Γ q.1.1 q.1.2 * q.2 := rfl

variable {G Γ}

theorem mem_dblBall_succ_of_mem {S : Finset G} {r : ℕ} {x : SymmetricDouble G Γ}
    (hx : x ∈ dblBall G Γ S r) : x ∈ dblBall G Γ S (r + 1) := by
  rw [dblBall_succ]
  exact Finset.mem_union_left _ hx

theorem letter_mem_dblBall {S : Finset G} {r : ℕ} {x : SymmetricDouble G Γ} (b : Bool) {g : G}
    (hg : g ∈ S) (hx : x ∈ dblBall G Γ S r) :
    inDouble G Γ b g * x ∈ dblBall G Γ S (r + 1) := by
  rw [dblBall_succ]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨((b, g), x), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ b, hg⟩, hx⟩,
      rfl⟩)

theorem dblBall_mono {S : Finset G} {r r' : ℕ} (h : r ≤ r') {x : SymmetricDouble G Γ}
    (hx : x ∈ dblBall G Γ S r) : x ∈ dblBall G Γ S r' := by
  induction h with
  | refl => exact hx
  | step _ ih => exact mem_dblBall_succ_of_mem ih

/-- A word with letters from `S` lies in the ball of its length. -/
theorem wordEval_mem_dblBall {S : Finset G} (l : List (Bool × G)) (hl : ∀ p, p ∈ l → p.2 ∈ S) :
    wordEval G (fun b g => inDouble G Γ b g) l ∈ dblBall G Γ S l.length := by
  induction l with
  | nil =>
    rw [wordEval_nil, dblBall_zero]
    exact Finset.mem_singleton_self 1
  | cons p l ih =>
    rw [wordEval_cons, List.length_cons]
    exact letter_mem_dblBall p.1 (hl p (List.mem_cons.mpr (Or.inl rfl)))
      (ih fun q hq => hl q (List.mem_cons.mpr (Or.inr hq)))

end Balls

end

end GroupApproximation.Full.NN01b
