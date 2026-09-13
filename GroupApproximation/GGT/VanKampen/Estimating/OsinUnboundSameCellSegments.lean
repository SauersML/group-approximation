import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCell
import Mathlib.Algebra.BigOperators.Intervals
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the scan along a cell word

The same-cell count scans a cell word from position `0` to position `n`.
* The positions of bound darts cut the word into segments.
* Inside a segment, every same-cell position lies in a closed pocket block, and every pocket block
  has value one.
* The letters that survive are those at the other unbound positions.

Each segment is a stretch of a `(λ, c)`-quasi-geodesic word that spells the same element as its
surviving letters, so the stretch bound applies to it.  Summing over the segments gives
`λ · #same ≤ (1 - λ) · #other + c · (1 + #segment starts)`.

This module is about positions only.  The dart instantiation is in `OsinUnboundSameCellCount`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open scoped Classical in
/-- The number of positions `j` with `k ≤ j < n` and `p j`, as a real number. -/
noncomputable def positionCount (p : ℕ → Prop) (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k n, if p j then (1 : ℝ) else 0

theorem positionCount_self (p : ℕ → Prop) (n : ℕ) : positionCount p n n = 0 := by
  simp [positionCount]

theorem positionCount_nonneg (p : ℕ → Prop) (k n : ℕ) : 0 ≤ positionCount p k n := by
  unfold positionCount
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem positionCount_split (p : ℕ → Prop) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    positionCount p k n = positionCount p k m + positionCount p m n := by
  unfold positionCount
  exact (Finset.sum_Ico_consecutive _ hkm hmn).symm

theorem positionCount_le_sub (p : ℕ → Prop) (k m : ℕ) :
    positionCount p k m ≤ ((m - k : ℕ) : ℝ) := by
  unfold positionCount
  calc _ ≤ ∑ _ ∈ Finset.Ico k m, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = ((m - k : ℕ) : ℝ) := by simp

theorem positionCount_succ_of_pos (p : ℕ → Prop) {k n : ℕ} (hk : k < n) (hp : p k) :
    positionCount p k n = 1 + positionCount p (k + 1) n := by
  unfold positionCount
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  simp [hp]

theorem positionCount_succ_of_neg (p : ℕ → Prop) {k n : ℕ} (hk : k < n) (hp : ¬ p k) :
    positionCount p k n = positionCount p (k + 1) n := by
  unfold positionCount
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  simp [hp]

theorem positionCount_succ_le (p : ℕ → Prop) {k n : ℕ} (hk : k < n) :
    positionCount p (k + 1) n ≤ positionCount p k n := by
  by_cases hp : p k
  · have h := positionCount_succ_of_pos p hk hp
    linarith
  · have h := positionCount_succ_of_neg p hk hp
    linarith

/-- **The letters of a stretch of a word indexed by positions.** -/
theorem take_drop_map_range {α : Type*} (w : ℕ → α) {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (((List.range n).map w).drop i).take (j - i) = (List.range' i (j - i)).map w := by
  rw [← List.map_drop, ← List.map_take, List.range_eq_range', List.drop_range',
    List.take_range'_of_length_ge (n := n - i) (k := j - i) (by omega)]
  simp

section Scan

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- **The scan along a quasi-geodesic word.**  Let `block k s` mark closed blocks `k, …, s` of
value one that do not cross, let every same position start or end a block, and let no same
position and no block end be bound.  Then
`λ · #same ≤ (1 - λ) · #(unbound, not same) + c · (1 + #segment starts)`. -/
theorem IsLambdaCQuasiGeodesicWord.scan_le
    {w : ℕ → RelLetter G Lambda} {n : ℕ}
    (hword : IsLambdaCQuasiGeodesicWord D lambda c ((List.range n).map w))
    (hlam0 : 0 ≤ lambda) (hlam1 : lambda ≤ 1)
    (same bound : ℕ → Prop) (block : ℕ → ℕ → Prop)
    (hblock : ∀ k s, block k s → k < s ∧ s < n)
    (hnest : ∀ k s k' s', block k s → block k' s' → k ≤ k' → k' ≤ s → s' ≤ s)
    (hone : ∀ k s, block k s → RelLetter.listVal ((List.range' k (s + 1 - k)).map w) = 1)
    (hcover : ∀ k, k < n → same k → (∃ s, block k s) ∨ ∃ k', k' < k ∧ block k' k)
    (hend : ∀ k s, block k s → ¬ bound s)
    (hsame : ∀ k, same k → ¬ bound k) :
    lambda * positionCount same 0 n ≤
      (1 - lambda) * positionCount (fun j => ¬ same j ∧ ¬ bound j) 0 n +
        c * (1 + positionCount (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) 0 n) := by
  have hlen : ((List.range n).map w).length = n := by simp
  have hc : 0 ≤ c := by
    have h := hword.stretch_le_length (i := 0) (j := 0) le_rfl (Nat.zero_le _) (alt := [])
      (fun a ha => by simp at ha) (by simp)
    simp at h
    linarith
  -- The scan state at position `k`: the open segment starts at `i`, its surviving letters are
  -- `alt`, no block straddles `k`, and a nonempty segment has no bound position before `k`.
  have key : ∀ t k, n - k = t → k ≤ n → ∀ (i : ℕ) (alt : List (RelLetter G Lambda)), i ≤ k →
      HullSC.RelWord.IsAdmissible D alt →
      RelLetter.listVal ((List.range' i (k - i)).map w) = RelLetter.listVal alt →
      (∀ k' s', block k' s' → k' < k → k ≤ s' → False) →
      (i < k → ¬ bound (k - 1)) →
      lambda * positionCount same k n + lambda * ((k - i : ℕ) : ℝ) ≤
        (1 - lambda) * positionCount (fun j => ¬ same j ∧ ¬ bound j) k n + (alt.length : ℝ) +
          c * (1 + positionCount (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) k n) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
    intro k hkt hkn i alt hik halt hval hinv hprev
    rcases Nat.lt_or_ge k n with hk | hk
    swap
    · -- The end of the word closes the last segment.
      have hkn' : k = n := le_antisymm hkn hk
      rw [hkn'] at hik hval
      rw [hkn']
      simp only [positionCount_self]
      have h := hword.stretch_le_length hik hlen.symm.le halt
        (by rw [take_drop_map_range w hik le_rfl]; exact hval)
      linarith
    by_cases hblk : ∃ s, block k s
    · -- A block starts at `k`: skip it.
      obtain ⟨s, hs⟩ := hblk
      obtain ⟨hks, hsn⟩ := hblock k s hs
      have ih' := ih (n - (s + 1)) (by omega) (s + 1) rfl (by omega) i alt (by omega) halt
        (by
          have hsplit : List.range' i (s + 1 - i) =
              List.range' i (k - i) ++ List.range' k (s + 1 - k) := by
            have h := List.range'_append_1 (s := i) (m := k - i) (n := s + 1 - k)
            rw [show i + (k - i) = k by omega, show k - i + (s + 1 - k) = s + 1 - i by omega]
              at h
            exact h.symm
          rw [hsplit, List.map_append, OsinComponents.listVal_append, hval, hone k s hs, mul_one])
        (fun k' s' hb hk' hs' => by
          rcases Nat.lt_or_ge k' k with hk'k | hk'k
          · exact hinv k' s' hb hk'k (by omega)
          · have h := hnest k s k' s' hs hb hk'k (by omega)
            omega)
        (fun _ => by rw [Nat.add_sub_cancel]; exact hend k s hs)
      have hcast : ((s + 1 - i : ℕ) : ℝ) = ((s + 1 - k : ℕ) : ℝ) + ((k - i : ℕ) : ℝ) := by
        rw [← Nat.cast_add]
        congr 1
        omega
      rw [hcast] at ih'
      rw [positionCount_split same (by omega : k ≤ s + 1) (by omega : s + 1 ≤ n),
        positionCount_split (fun j => ¬ same j ∧ ¬ bound j) (by omega : k ≤ s + 1)
          (by omega : s + 1 ≤ n),
        positionCount_split (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) (by omega : k ≤ s + 1)
          (by omega : s + 1 ≤ n)]
      have h1 := mul_le_mul_of_nonneg_left (positionCount_le_sub same k (s + 1)) hlam0
      have h2 := mul_nonneg (sub_nonneg.mpr hlam1)
        (positionCount_nonneg (fun j => ¬ same j ∧ ¬ bound j) k (s + 1))
      have h3 := mul_nonneg hc
        (positionCount_nonneg (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) k (s + 1))
      linarith
    -- No block straddles `k + 1`.
    have hinv' : ∀ k' s', block k' s' → k' < k + 1 → k + 1 ≤ s' → False := by
      intro k' s' hb hk' hs'
      rcases Nat.lt_or_ge k' k with hk'k | hk'k
      · exact hinv k' s' hb hk'k (by omega)
      · exact hblk ⟨s', by rwa [show k' = k by omega] at hb⟩
    have hTk := positionCount_succ_le (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) hk
    have hTc := mul_le_mul_of_nonneg_left hTk hc
    by_cases hb : bound k
    · -- A bound position closes the segment and opens an empty one.
      have hnot : ¬ same k := fun h => hsame k h hb
      have ih' := ih (n - (k + 1)) (by omega) (k + 1) rfl (by omega) (k + 1) [] le_rfl
        (fun a ha => by simp at ha) (by simp) hinv' (fun h => absurd h (lt_irrefl _))
      have e0 : ((k + 1 - (k + 1) : ℕ) : ℝ) = 0 := by simp
      have e1 : (([] : List (RelLetter G Lambda)).length : ℝ) = 0 := by simp
      rw [e0, e1] at ih'
      rw [positionCount_succ_of_neg same hk hnot,
        positionCount_succ_of_neg (fun j => ¬ same j ∧ ¬ bound j) hk (fun h => h.2 hb)]
      rcases Nat.lt_or_ge i k with hik' | hik'
      · have hstart : 0 < k ∧ bound k ∧ ¬ bound (k - 1) := ⟨by omega, hb, hprev hik'⟩
        rw [positionCount_succ_of_pos (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) hk hstart]
        have h := hword.stretch_le_length hik (hkn.trans hlen.symm.le) halt
          (by rw [take_drop_map_range w hik hkn]; exact hval)
        linarith
      · have e2 : ((k - i : ℕ) : ℝ) = 0 := by rw [show k - i = 0 by omega, Nat.cast_zero]
        rw [e2]
        have hL : (0 : ℝ) ≤ alt.length := Nat.cast_nonneg _
        linarith
    · -- An unbound position outside every block survives.
      have hnot : ¬ same k := by
        intro h
        rcases hcover k hk h with h' | ⟨k', hk', hb'⟩
        · exact hblk h'
        · exact hinv k' k hb' hk' le_rfl
      have ih' := ih (n - (k + 1)) (by omega) (k + 1) rfl (by omega) i (alt ++ [w k]) (by omega)
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact halt a ha
          · rw [List.mem_singleton] at ha
            rw [ha]
            exact hword.1 (w k) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
        (by
          have hsplit : List.range' i (k + 1 - i) = List.range' i (k - i) ++ [k] := by
            have h := List.range'_append_1 (s := i) (m := k - i) (n := 1)
            rw [show i + (k - i) = k by omega, show k - i + 1 = k + 1 - i by omega,
              List.range'_one] at h
            exact h.symm
          rw [hsplit, List.map_append, OsinComponents.listVal_append, hval, List.map_cons,
            List.map_nil, OsinComponents.listVal_append])
        hinv' (fun _ => by rw [Nat.add_sub_cancel]; exact hb)
      have e1 : ((k + 1 - i : ℕ) : ℝ) = ((k - i : ℕ) : ℝ) + 1 := by
        rw [show k + 1 - i = (k - i) + 1 by omega, Nat.cast_add, Nat.cast_one]
      have e2 : (((alt ++ [w k]).length : ℕ) : ℝ) = (alt.length : ℝ) + 1 := by simp
      rw [e1, e2] at ih'
      rw [positionCount_succ_of_neg same hk hnot,
        positionCount_succ_of_pos (fun j => ¬ same j ∧ ¬ bound j) hk ⟨hnot, hb⟩]
      linarith
  have h := key (n - 0) 0 rfl (Nat.zero_le n) 0 [] le_rfl (fun a ha => by simp at ha) (by simp)
    (fun k' _ _ hk' _ => Nat.not_lt_zero k' hk') (fun h => absurd h (lt_irrefl 0))
  have e0 : ((0 - 0 : ℕ) : ℝ) = 0 := by simp
  have e1 : (([] : List (RelLetter G Lambda)).length : ℝ) = 0 := by simp
  rw [e0, e1] at h
  linarith

end Scan

/-- **Printed endpoint.**  The scan bound along a `(λ, c)`-quasi-geodesic word whose same
positions are covered by non-crossing blocks of value one. -/
def OsinUnboundSameCellScanBound : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (w : ℕ → RelLetter G Lambda) (n : ℕ),
    IsLambdaCQuasiGeodesicWord D lambda c ((List.range n).map w) → 0 ≤ lambda → lambda ≤ 1 →
    ∀ (same bound : ℕ → Prop) (block : ℕ → ℕ → Prop),
      (∀ k s, block k s → k < s ∧ s < n) →
      (∀ k s k' s', block k s → block k' s' → k ≤ k' → k' ≤ s → s' ≤ s) →
      (∀ k s, block k s → RelLetter.listVal ((List.range' k (s + 1 - k)).map w) = 1) →
      (∀ k, k < n → same k → (∃ s, block k s) ∨ ∃ k', k' < k ∧ block k' k) →
      (∀ k s, block k s → ¬ bound s) →
      (∀ k, same k → ¬ bound k) →
      lambda * positionCount same 0 n ≤
        (1 - lambda) * positionCount (fun j => ¬ same j ∧ ¬ bound j) 0 n +
          c * (1 + positionCount (fun j => 0 < j ∧ bound j ∧ ¬ bound (j - 1)) 0 n)

theorem osinUnboundSameCellScanBound_holds : OsinUnboundSameCellScanBound.{u, w} := by
  intro G _ Lambda D lambda c w n hword hlam0 hlam1 same bound block hblock hnest hone hcover
    hend hsame
  exact hword.scan_le hlam0 hlam1 same bound block hblock hnest hone hcover hend hsame

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinUnboundSameCellScanBound_holds
