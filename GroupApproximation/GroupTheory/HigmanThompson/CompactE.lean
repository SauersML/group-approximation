import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HigmanThompson.Generators
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's conjugacy from the half line onto a bounded interval

Brown's isomorphism `F_{n,r} ≅ F_{n,∞}` conjugates by a piecewise linear bijection
`E : [0, ∞) → [0, r)` whose breakpoints accumulate at `r`.  This module builds `E` on all of
`ℚ` (`compE m r`, `n = m + 2`): the identity on `(-∞, r-1]`, and on the `i`-th block
`[r - 1 + i(n-1), r - 1 + (i+1)(n-1)]` the affine map onto `[r - n^{-i}, r - n^{-(i+1)}]`
with slope `n^{-(i+1)}` (`compE_block`).

* `compE_strictMono`, `compE_lt`, `compE_surj`: `E` is a strictly increasing bijection of
  `ℚ` onto `(-∞, r)`.
* `compE_add_q`, `compE_add_nat_q`: translating by `k(n-1)` on the half line is scaling
  the distance to `r` by `n^{-k}`.  This is how an eventual translation of `F_{n,∞}`
  becomes an affine germ at `r` in `F_{n,r}`.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m r : ℕ)

theorem mOne_pos : (0 : ℚ) < (m : ℚ) + 1 := by positivity

/-- The block index `⌊v / (m+1)⌋`. -/
noncomputable def blk (v : ℚ) : ℕ := (⌊v / ((m : ℚ) + 1)⌋).toNat

theorem blk_spec {v : ℚ} (hv : 0 ≤ v) :
    (blk m v : ℚ) * ((m : ℚ) + 1) ≤ v ∧ v < ((blk m v : ℚ) + 1) * ((m : ℚ) + 1) := by
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  have hfl0 : 0 ≤ ⌊v / ((m : ℚ) + 1)⌋ := Int.floor_nonneg.mpr (div_nonneg hv hq.le)
  have hcast : ((blk m v : ℕ) : ℚ) = ((⌊v / ((m : ℚ) + 1)⌋ : ℤ) : ℚ) := by
    unfold blk
    have h := Int.toNat_of_nonneg hfl0
    exact_mod_cast h
  rw [hcast]
  constructor
  · have h := Int.floor_le (v / ((m : ℚ) + 1))
    rwa [le_div_iff₀ hq] at h
  · have h := Int.lt_floor_add_one (v / ((m : ℚ) + 1))
    rwa [div_lt_iff₀ hq] at h

/-- **Brown's conjugacy** `E`. -/
noncomputable def compE (u : ℚ) : ℚ :=
  if u ≤ (r : ℚ) - 1 then u else
    (r : ℚ) - (((m : ℚ) + 2) ^ blk m (u - ((r : ℚ) - 1)))⁻¹ +
      (u - ((r : ℚ) - 1) - (blk m (u - ((r : ℚ) - 1)) : ℚ) * ((m : ℚ) + 1)) *
        (((m : ℚ) + 2) ^ (blk m (u - ((r : ℚ) - 1)) + 1))⁻¹

theorem compE_of_le {u : ℚ} (h : u ≤ (r : ℚ) - 1) : compE m r u = u := by
  simp [compE, h]

theorem block_end_eq (i : ℕ) :
    (((m : ℚ) + 2) ^ i)⁻¹ - ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ (i + 1))⁻¹ =
      (((m : ℚ) + 2) ^ (i + 1))⁻¹ := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  field_simp
  ring

/-- **The blocks.** -/
theorem compE_block (i : ℕ) {w : ℚ} (hw0 : 0 ≤ w) (hw1 : w ≤ (m : ℚ) + 1) :
    compE m r ((r : ℚ) - 1 + i * ((m : ℚ) + 1) + w) =
      (r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹ + w * (((m : ℚ) + 2) ^ (i + 1))⁻¹ := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  unfold compE
  split_ifs with h
  · have hi0 : (0 : ℚ) ≤ (i : ℚ) * ((m : ℚ) + 1) := by positivity
    have hw : w = 0 := by linarith
    have hiq0 : (i : ℚ) * ((m : ℚ) + 1) = 0 := by linarith
    have hi : (i : ℚ) = 0 := by
      rcases mul_eq_zero.mp hiq0 with h' | h'
      · exact h'
      · exact absurd h' hq.ne'
    have hin : i = 0 := by exact_mod_cast hi
    subst hin
    rw [hw]
    simp
  · have hv : (r : ℚ) - 1 + i * ((m : ℚ) + 1) + w - ((r : ℚ) - 1) = i * ((m : ℚ) + 1) + w := by
      ring
    rw [hv]
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · have hblk : blk m ((i : ℚ) * ((m : ℚ) + 1) + w) = i := by
        unfold blk
        have hfl : ⌊((i : ℚ) * ((m : ℚ) + 1) + w) / ((m : ℚ) + 1)⌋ = (i : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor
          · rw [le_div_iff₀ hq]
            push_cast
            linarith
          · rw [div_lt_iff₀ hq]
            push_cast
            linarith
        rw [hfl]
        simp
      rw [hblk]
      ring
    · have hblk : blk m ((i : ℚ) * ((m : ℚ) + 1) + w) = i + 1 := by
        unfold blk
        have hfl : ⌊((i : ℚ) * ((m : ℚ) + 1) + w) / ((m : ℚ) + 1)⌋ = ((i + 1 : ℕ) : ℤ) := by
          rw [heq, Int.floor_eq_iff]
          constructor
          · rw [le_div_iff₀ hq]
            push_cast
            linarith
          · rw [div_lt_iff₀ hq]
            push_cast
            linarith
        rw [hfl]
        simp
      rw [hblk, heq]
      have e := block_end_eq m i
      push_cast
      linear_combination e

theorem exists_block {u : ℚ} (hu : (r : ℚ) - 1 ≤ u) : ∃ i : ℕ, ∃ w : ℚ, 0 ≤ w ∧
    w < (m : ℚ) + 1 ∧ u = (r : ℚ) - 1 + i * ((m : ℚ) + 1) + w := by
  have hb := blk_spec m (sub_nonneg.mpr hu)
  refine ⟨blk m (u - ((r : ℚ) - 1)),
    u - ((r : ℚ) - 1) - (blk m (u - ((r : ℚ) - 1)) : ℚ) * ((m : ℚ) + 1), ?_, ?_, by ring⟩
  · linarith [hb.1]
  · linarith [hb.2]

theorem compE_lt (u : ℚ) : compE m r u < r := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  rcases le_or_lt u ((r : ℚ) - 1) with h | h
  · rw [compE_of_le m r h]
    linarith
  obtain ⟨i, w, hw0, hwq, rfl⟩ := exists_block m r h.le
  rw [compE_block m r i hw0 hwq.le]
  have e := block_end_eq m i
  have hpi : 0 < (((m : ℚ) + 2) ^ (i + 1))⁻¹ := inv_pos.mpr (pow_pos hp _)
  nlinarith

/-- A block value above `r - 1`. -/
theorem lt_compE_of_gt {u : ℚ} (h : (r : ℚ) - 1 < u) : (r : ℚ) - 1 < compE m r u := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  obtain ⟨i, w, hw0, hwq, rfl⟩ := exists_block m r h.le
  rw [compE_block m r i hw0 hwq.le]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have hw : 0 < w := by
      by_contra hw'
      have : w = 0 := le_antisymm (not_lt.mp hw') hw0
      simp [this] at h
    simp only [pow_zero, inv_one, zero_add, pow_one]
    have hpi : 0 < ((m : ℚ) + 2)⁻¹ := inv_pos.mpr hp
    nlinarith
  · have h1 : (((m : ℚ) + 2) ^ i)⁻¹ < 1 := by
      rw [inv_lt_one₀ (pow_pos hp _)]
      exact one_lt_pow₀ (by linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]) hi.ne'
    have hpi : 0 < (((m : ℚ) + 2) ^ (i + 1))⁻¹ := inv_pos.mpr (pow_pos hp _)
    nlinarith

theorem inv_pow_antitone {i j : ℕ} (hij : i ≤ j) :
    (((m : ℚ) + 2) ^ j)⁻¹ ≤ (((m : ℚ) + 2) ^ i)⁻¹ := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  rw [inv_le_inv₀ (pow_pos hp _) (pow_pos hp _)]
  exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]) hij

theorem compE_strictMono : StrictMono (compE m r) := by
  intro u u' huu'
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  rcases le_or_lt u' ((r : ℚ) - 1) with h' | h'
  · rw [compE_of_le m r (le_trans huu'.le h'), compE_of_le m r h']
    exact huu'
  rcases le_or_lt u ((r : ℚ) - 1) with h | h
  · rw [compE_of_le m r h]
    exact lt_of_le_of_lt h (lt_compE_of_gt m r h')
  obtain ⟨i, w, hw0, hwq, rfl⟩ := exists_block m r h.le
  obtain ⟨i', w', hw0', hwq', rfl⟩ := exists_block m r h'.le
  rw [compE_block m r i hw0 hwq.le, compE_block m r i' hw0' hwq'.le]
  have hpi : 0 < (((m : ℚ) + 2) ^ (i + 1))⁻¹ := inv_pos.mpr (pow_pos hp _)
  rcases lt_trichotomy i i' with hii | rfl | hii
  · have e := block_end_eq m i
    have hmono := inv_pow_antitone m (show i + 1 ≤ i' from hii)
    have hpi' : 0 ≤ w' * (((m : ℚ) + 2) ^ (i' + 1))⁻¹ :=
      mul_nonneg hw0' (inv_pos.mpr (pow_pos hp _)).le
    nlinarith
  · have hww : w < w' := by linarith
    nlinarith
  · exfalso
    have h1 : (i' : ℚ) + 1 ≤ i := by
      have h2 : i' + 1 ≤ i := hii
      exact_mod_cast h2
    nlinarith

theorem compE_surj {t : ℚ} (ht : t < r) : ∃ u, compE m r u = t := by
  rcases le_or_lt t ((r : ℚ) - 1) with h | h
  · exact ⟨t, compE_of_le m r h⟩
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hp1 : (1 : ℚ) < (m : ℚ) + 2 := by linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
  have hpos : (0 : ℚ) < (r : ℚ) - t := by linarith
  have hex : ∃ j : ℕ, (((m : ℚ) + 2) ^ (j + 1))⁻¹ < (r : ℚ) - t := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((r : ℚ) - t)⁻¹ hp1
    refine ⟨j, ?_⟩
    rw [inv_lt_comm₀ (pow_pos hp _) hpos]
    exact lt_of_lt_of_le hj (pow_le_pow_right₀ hp1.le (Nat.le_succ j))
  classical
  have hi : (((m : ℚ) + 2) ^ (Nat.find hex + 1))⁻¹ < (r : ℚ) - t := Nat.find_spec hex
  have hmin : (r : ℚ) - t ≤ (((m : ℚ) + 2) ^ (Nat.find hex))⁻¹ := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos'
    · rw [h0]
      simp only [pow_zero, inv_one]
      linarith
    · have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      have h2 := not_lt.mp hnot
      rwa [Nat.sub_add_cancel hpos'] at h2
  set i := Nat.find hex with hidef
  have hpi1 : (0 : ℚ) < ((m : ℚ) + 2) ^ (i + 1) := pow_pos hp _
  have e := block_end_eq m i
  refine ⟨(r : ℚ) - 1 + i * ((m : ℚ) + 1) +
    (t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹)) * ((m : ℚ) + 2) ^ (i + 1), ?_⟩
  have hw0 : 0 ≤ (t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹)) * ((m : ℚ) + 2) ^ (i + 1) :=
    mul_nonneg (by linarith) hpi1.le
  have hw1 : (t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹)) * ((m : ℚ) + 2) ^ (i + 1) ≤ (m : ℚ) + 1 := by
    have h1 : t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹) ≤ ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ (i + 1))⁻¹ := by
      linarith
    calc (t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹)) * ((m : ℚ) + 2) ^ (i + 1)
        ≤ ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ (i + 1))⁻¹ * ((m : ℚ) + 2) ^ (i + 1) :=
          mul_le_mul_of_nonneg_right h1 hpi1.le
      _ = (m : ℚ) + 1 := by field_simp
  rw [compE_block m r i hw0 hw1]
  have hinv : ((m : ℚ) + 2) ^ (i + 1) * (((m : ℚ) + 2) ^ (i + 1))⁻¹ = 1 :=
    mul_inv_cancel₀ hpi1.ne'
  linear_combination (t - ((r : ℚ) - (((m : ℚ) + 2) ^ i)⁻¹)) * hinv

/-- **Translation by `n - 1` on the half line is a contraction towards `r`.** -/
theorem compE_add_q {u : ℚ} (hu : (r : ℚ) - 1 ≤ u) :
    compE m r (u + ((m : ℚ) + 1)) = (r : ℚ) - ((r : ℚ) - compE m r u) / ((m : ℚ) + 2) := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  obtain ⟨i, w, hw0, hwq, rfl⟩ := exists_block m r hu
  have e : (r : ℚ) - 1 + i * ((m : ℚ) + 1) + w + ((m : ℚ) + 1) =
      (r : ℚ) - 1 + ((i + 1 : ℕ) : ℚ) * ((m : ℚ) + 1) + w := by
    push_cast
    ring
  rw [e, compE_block m r (i + 1) hw0 hwq.le, compE_block m r i hw0 hwq.le]
  field_simp
  ring

theorem compE_add_nat_q (k : ℕ) {u : ℚ} (hu : (r : ℚ) - 1 ≤ u) :
    compE m r (u + k * ((m : ℚ) + 1)) = (r : ℚ) - ((r : ℚ) - compE m r u) / ((m : ℚ) + 2) ^ k := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  induction k with
  | zero => simp
  | succ k ih =>
    have e : u + ((k + 1 : ℕ) : ℚ) * ((m : ℚ) + 1) = (u + k * ((m : ℚ) + 1)) + ((m : ℚ) + 1) := by
      push_cast
      ring
    have hk0 : (0 : ℚ) ≤ (k : ℚ) * ((m : ℚ) + 1) := by positivity
    rw [e, compE_add_q m r (by linarith), ih]
    field_simp
    ring

#audit_axioms GroupApproximation.HigmanThompson.compE_strictMono
#audit_axioms GroupApproximation.HigmanThompson.compE_add_nat_q

end HigmanThompson
end GroupApproximation
