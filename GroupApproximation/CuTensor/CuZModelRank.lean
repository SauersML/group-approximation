import GroupApproximation.CuTensor.CuZModelCompact
import GroupApproximation.CuTensor.CuZAxioms

/-!
# The rank of a class in the model of `Cu(𝒵)`

The rank of the compact class `n` is `n` and the rank of the soft class `t` is `t`.  The rank is
monotone and additive, and a class of strictly smaller rank lies below.  This file proves that
addition in the model is monotone and that every sequence of classes has a supremum (axiom O1),
whose rank is the supremum of the ranks.

## Main results

* `CuZModel.rank_mono`, `CuZModel.rank_add`, `CuZModel.le_of_rank_lt`;
* `CuZModel.add_mono`: addition is monotone;
* `CuZModel.exists_isLUB_range`: every sequence has a supremum;
* `CuZModel.rank_eq_iSup`: the rank of a supremum is the supremum of the ranks.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor
namespace CuZModel

/-- The rank of a class: `n` on the compact class `n`, `t` on the soft class `t`. -/
def rank : CuZModel → ℝ≥0∞
  | cpt n => n
  | soft t _ => t

@[simp] theorem rank_cpt (n : ℕ) : rank (cpt n) = n := rfl

@[simp] theorem rank_soft (t : ℝ≥0∞) (ht : 0 < t) : rank (soft t ht) = t := rfl

/-- The rank is monotone. -/
theorem rank_mono : Monotone rank := by
  intro x y h
  cases x with
  | cpt m =>
    cases y with
    | cpt n =>
      show (m : ℝ≥0∞) ≤ (n : ℝ≥0∞)
      exact Nat.cast_le.2 (cpt_le_cpt.1 h)
    | soft t ht => exact (cpt_le_soft.1 h).le
  | soft s hs =>
    cases y with
    | cpt n => exact soft_le_cpt.1 h
    | soft t ht => exact soft_le_soft.1 h

/-- The rank is additive. -/
theorem rank_add : ∀ x y : CuZModel, rank (x + y) = rank x + rank y
  | cpt m, cpt n => by rw [cpt_add_cpt, rank_cpt, rank_cpt, rank_cpt, Nat.cast_add]
  | cpt _, soft _ _ => rfl
  | soft _ _, cpt _ => rfl
  | soft _ _, soft _ _ => rfl

theorem soft_congr {s t : ℝ≥0∞} {hs : 0 < s} {ht : 0 < t} (h : s = t) :
    soft s hs = soft t ht := by
  subst h
  rfl

/-- A soft class lies below a class exactly when its rank does. -/
theorem soft_le_iff {t : ℝ≥0∞} {ht : 0 < t} {z : CuZModel} : soft t ht ≤ z ↔ t ≤ rank z := by
  cases z <;> exact Iff.rfl

theorem soft_add (t : ℝ≥0∞) (ht : 0 < t) :
    ∀ x : CuZModel, soft t ht + x = soft (t + rank x) (lt_of_lt_of_le ht le_self_add)
  | cpt _ => rfl
  | soft _ _ => rfl

theorem add_soft (t : ℝ≥0∞) (ht : 0 < t) :
    ∀ x : CuZModel, x + soft t ht = soft (rank x + t) (lt_of_lt_of_le ht le_add_self)
  | cpt _ => rfl
  | soft _ _ => rfl

/-- A class of strictly smaller rank lies below. -/
theorem le_of_rank_lt {x y : CuZModel} (h : rank x < rank y) : x ≤ y := by
  cases x with
  | cpt m =>
    cases y with
    | cpt n => exact cpt_le_cpt.2 (Nat.cast_lt.1 (show (m : ℝ≥0∞) < n from h)).le
    | soft t ht => exact cpt_le_soft.2 h
  | soft s hs =>
    cases y with
    | cpt n => exact soft_le_cpt.2 h.le
    | soft t ht => exact soft_le_soft.2 h.le

/-- A strict inequality either raises the rank or ends at a compact class. -/
theorem rank_lt_or_eq_cpt {x y : CuZModel} (hxy : x ≤ y) (hyx : ¬ y ≤ x) :
    rank x < rank y ∨ ∃ n, y = cpt n := by
  cases y with
  | cpt n => exact Or.inr ⟨n, rfl⟩
  | soft t ht =>
    cases x with
    | cpt m => exact Or.inl (cpt_le_soft.1 hxy)
    | soft s hs =>
      exact Or.inl (lt_of_le_of_ne (soft_le_soft.1 hxy) fun h => hyx (soft_le_soft.2 h.symm.le))

/-- A strict inequality above a compact class raises the rank. -/
theorem rank_cpt_lt {n : ℕ} {z : CuZModel} (hnz : cpt n ≤ z) (hzn : ¬ z ≤ cpt n) :
    rank (cpt n) < rank z := by
  cases z with
  | cpt k =>
    show (n : ℝ≥0∞) < (k : ℝ≥0∞)
    exact Nat.cast_lt.2 (lt_of_le_of_ne (cpt_le_cpt.1 hnz) fun h => hzn (cpt_le_cpt.2 h.symm.le))
  | soft t ht => exact cpt_le_soft.1 hnz

/-- Two strict inequalities raise the rank. -/
theorem rank_lt_of_lt_of_lt {x y z : CuZModel} (hxy : x ≤ y) (hyx : ¬ y ≤ x) (hyz : y ≤ z)
    (hzy : ¬ z ≤ y) : rank x < rank z := by
  rcases rank_lt_or_eq_cpt hxy hyx with h | ⟨n, rfl⟩
  · exact lt_of_lt_of_le h (rank_mono hyz)
  · exact lt_of_le_of_lt (rank_mono hxy) (rank_cpt_lt hyz hzy)

/-- **Addition in the model is monotone.** -/
theorem add_mono {x y x' y' : CuZModel} (h : x ≤ y) (h' : x' ≤ y') : x + x' ≤ y + y' := by
  cases x with
  | soft t ht =>
    rw [soft_add, soft_le_iff, rank_add]
    exact add_le_add (rank_mono h) (rank_mono h')
  | cpt a =>
    cases x' with
    | soft t ht =>
      rw [add_soft, soft_le_iff, rank_add]
      exact add_le_add (rank_mono h) (rank_mono h')
    | cpt b =>
      cases y with
      | soft t ht =>
        rw [cpt_add_cpt, soft_add, cpt_le_soft, Nat.cast_add]
        exact ENNReal.add_lt_add_of_lt_of_le (ENNReal.natCast_ne_top b) (cpt_le_soft.1 h)
          (rank_mono h')
      | cpt c =>
        cases y' with
        | cpt d => exact cpt_le_cpt.2 (Nat.add_le_add (cpt_le_cpt.1 h) (cpt_le_cpt.1 h'))
        | soft t ht =>
          rw [cpt_add_cpt, add_soft, cpt_le_soft, Nat.cast_add]
          exact ENNReal.add_lt_add_of_le_of_lt (ENNReal.natCast_ne_top a) (rank_mono h)
            (cpt_le_soft.1 h')

/-- **(O1) Every sequence of classes has a supremum.** Either some term dominates the sequence,
or the ranks never reach their supremum `D` and the soft class `D` is the supremum. -/
theorem exists_isLUB_range (f : ℕ → CuZModel) : ∃ s, IsLUB (Set.range f) s := by
  by_cases hmax : ∃ k, ∀ j, f j ≤ f k
  · obtain ⟨k, hk⟩ := hmax
    refine ⟨f k, ?_, fun b hb => hb (Set.mem_range_self k)⟩
    rintro _ ⟨j, rfl⟩
    exact hk j
  · have hstep : ∀ k, ∃ j, f k ≤ f j ∧ ¬ f j ≤ f k := fun k => by
      obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hmax k)
      exact ⟨j, (le_total' (f j) (f k)).resolve_left hj, hj⟩
    have hlt : ∀ k, rank (f k) < ⨆ j, rank (f j) := fun k => by
      obtain ⟨j, hkj, hjk⟩ := hstep k
      obtain ⟨j', hjj', hj'j⟩ := hstep j
      exact lt_of_lt_of_le (rank_lt_of_lt_of_lt hkj hjk hjj' hj'j)
        (le_iSup (fun j => rank (f j)) j')
    have hpos : 0 < ⨆ j, rank (f j) := lt_of_le_of_lt zero_le (hlt 0)
    refine ⟨soft (⨆ j, rank (f j)) hpos, ?_, fun b hb => ?_⟩
    · rintro _ ⟨k, rfl⟩
      exact le_of_rank_lt (hlt k)
    · exact soft_le_iff.2 (iSup_le fun k => rank_mono (hb (Set.mem_range_self k)))

/-- **The rank of a supremum is the supremum of the ranks.** -/
theorem rank_eq_iSup {f : ℕ → CuZModel} {s : CuZModel} (hs : IsLUB (Set.range f) s) :
    rank s = ⨆ n, rank (f n) := by
  refine le_antisymm ?_ (iSup_le fun n => rank_mono (hs.1 (Set.mem_range_self n)))
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr, hrs⟩ := exists_between hlt
  have hpos : 0 < r := lt_of_le_of_lt zero_le hr
  have hub : soft r hpos ∈ upperBounds (Set.range f) := by
    rintro _ ⟨n, rfl⟩
    exact le_of_rank_lt (lt_of_le_of_lt (le_iSup (fun n => rank (f n)) n) hr)
  exact absurd (rank_mono (hs.2 hub)) (not_le.2 hrs)

end CuZModel

end CuTensor
end GroupApproximation
