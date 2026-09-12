import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HydeLodha.GammaTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# An element of `Γ₂` that does not preserve `ℤ`

Hyde–Lodha, proof of Proposition 3.4, for `n = 2`, `η = 6`: "For `I := [-1/η, n/η]`, we define
`λ : I → I` as follows: `[-6/36, -5/36] ↦ [-6/36, 0]` linear with slope `η`; `[-5/36, 0] ↦
[0, 10/36]` linear with slope `n`; `[0, 12/36] ↦ [10/36, 12/36]` linear with slope `1/η`.  Define
the `1`-periodic homeomorphism `f : ℝ → ℝ` satisfying `Supp(f) = Int(I) + ℤ` and `f ↾ I = λ`.
Clearly, `f ∈ Γ_n` and `ℤ` is not `f`-invariant."

Here `f` acts on `ℚ`.  On the period `[0, 1]` it reads, piece by piece (`lamOne`),

* `t/6 + 5/18` on `[0, 1/3]`  (the piece `[0, 12/36] ↦ [10/36, 12/36]`, slope `2⁻¹3⁻¹`),
* `t`          on `[1/3, 5/6]` (outside the support),
* `6t - 25/6`  on `[5/6, 31/36]` (the piece `[-6/36, -5/36] + 1`, slope `2·3`),
* `2t - 13/18` on `[31/36, 1]` (the piece `[-5/36, 0] + 1`, slope `2`, crossing the integer `1`),

and `lamFun t = ⌊t⌋ + lamOne (fract t)`.

* `lamPerm_mem_gammaTwo`: `f ∈ Γ₂`, including condition (3) on each piece (on the last piece
  `i - j = 1` and `f` moves `x` across one integer);
* `lamPerm_zero`: `f 0 = 5/18`, so `ℤ` is not `f`-invariant.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem mem_slopes23 {s : ℚ} : s ∈ slopes23 ↔ ∃ i j : ℤ, s = (2 : ℚ) ^ i * (3 : ℚ) ^ j :=
  Iff.rfl

/-! ## Periodic grid affinity -/

/-- A `1`-periodic map that is grid-affine on the level-`N` intervals of one period is grid-affine. -/
theorem gridAffine_six_of_periodic {f : ℚ → ℚ} {Ω : Submonoid ℚ} {N B : ℕ}
    (hper : ∀ (t : ℚ) (j : ℤ), f (t + j) = f t + j)
    (hslope : ∀ r : ℤ, 0 ≤ r → r < 6 ^ N →
      ∃ s ∈ Ω, s ∈ Grid 6 B ∧ AffineOn f (gridPt 6 N r) (gridPt 6 N (r + 1)) s)
    (hval : ∀ r : ℤ, 0 ≤ r → r < 6 ^ N → f (gridPt 6 N r) ∈ Grid 6 B) :
    GridAffine 6 Ω f N B := by
  have hpos : (0 : ℤ) < 6 ^ N := pow_pos (by norm_num) N
  have hden : ((6 : ℕ) : ℚ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have hshift : ∀ r q : ℤ, gridPt 6 N (r + q * 6 ^ N) = gridPt 6 N r + q := by
    intro r q
    unfold gridPt
    rw [div_add' _ _ _ hden, div_left_inj' hden]
    push_cast
    ring
  have hdec : ∀ k : ℤ, ∃ r q : ℤ, k = r + q * 6 ^ N ∧ 0 ≤ r ∧ r < 6 ^ N := fun k =>
    ⟨k % 6 ^ N, k / 6 ^ N, by rw [mul_comm]; exact (Int.emod_add_mul_ediv k (6 ^ N)).symm,
      Int.emod_nonneg k hpos.ne', Int.emod_lt_of_pos k hpos⟩
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨r, q, rfl, hr0, hr1⟩ := hdec k
    obtain ⟨s, hsΩ, hsB, haff⟩ := hslope r hr0 hr1
    refine ⟨s, hsΩ, hsB, fun t ht1 ht2 => ?_⟩
    have e2 : gridPt 6 N (r + q * 6 ^ N + 1) = gridPt 6 N (r + 1) + q := by
      rw [show r + q * 6 ^ N + 1 = (r + 1) + q * 6 ^ N by ring]
      exact hshift (r + 1) q
    rw [hshift] at ht1 ⊢
    rw [e2] at ht2
    have h := haff (t - q) (by linarith) (by linarith)
    have hft := hper (t - q) q
    rw [sub_add_cancel] at hft
    rw [hft, hper, h]
    ring
  · obtain ⟨r, q, rfl, hr0, hr1⟩ := hdec k
    rw [hshift, hper]
    exact grid_add (hval r hr0 hr1) (int_mem_grid B q)

/-! ## The map on one period -/

/-- The four affine pieces of `f` on `[0, 1]`. -/
def lamOne (s : ℚ) : ℚ :=
  if s ≤ 1 / 3 then s / 6 + 5 / 18 else if s ≤ 5 / 6 then s
    else if s ≤ 31 / 36 then 6 * s - 25 / 6 else 2 * s - 13 / 18

theorem lamOne_piece1 {s : ℚ} (h1 : s ≤ 1 / 3) : lamOne s = s / 6 + 5 / 18 := by
  simp only [lamOne, if_pos h1]

theorem lamOne_piece2 {s : ℚ} (h0 : 1 / 3 ≤ s) (h1 : s ≤ 5 / 6) : lamOne s = s := by
  unfold lamOne
  split_ifs <;> linarith

theorem lamOne_piece3 {s : ℚ} (h0 : 5 / 6 ≤ s) (h1 : s ≤ 31 / 36) : lamOne s = 6 * s - 25 / 6 := by
  unfold lamOne
  split_ifs <;> linarith

theorem lamOne_piece4 {s : ℚ} (h0 : 31 / 36 ≤ s) : lamOne s = 2 * s - 13 / 18 := by
  unfold lamOne
  split_ifs <;> linarith

theorem lamOne_ge {s : ℚ} (h0 : 0 ≤ s) : 5 / 18 ≤ lamOne s := by
  unfold lamOne
  split_ifs <;> linarith

theorem lamOne_lt {s : ℚ} (h1 : s < 1) : lamOne s < 23 / 18 := by
  unfold lamOne
  split_ifs <;> linarith

theorem lamOne_strictMono : StrictMono lamOne := by
  intro s s' hs
  unfold lamOne
  split_ifs <;> linarith

/-- **`f`**, the `1`-periodic extension. -/
def lamFun (t : ℚ) : ℚ := ⌊t⌋ + lamOne (Int.fract t)

theorem lamFun_add_int (t : ℚ) (k : ℤ) : lamFun (t + k) = lamFun t + k := by
  simp only [lamFun, Int.floor_add_intCast, Int.fract_add_intCast]
  push_cast
  ring

theorem lamFun_of_mem {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : lamFun t = lamOne t := by
  rcases lt_or_eq_of_le h1 with h1 | rfl
  · simp only [lamFun, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, Int.fract_eq_self.mpr ⟨h0, h1⟩]
    simp
  · simp only [lamFun, Int.floor_one, Int.fract_one]
    norm_num [lamOne]

theorem lamFun_strictMono : StrictMono lamFun := by
  intro t t' h
  unfold lamFun
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  have hf0' := Int.fract_nonneg t'
  rcases lt_or_eq_of_le (Int.floor_mono h.le) with hlt | heq
  · have h' : ⌊t⌋ + 1 ≤ ⌊t'⌋ := by omega
    have h'' : ((⌊t⌋ : ℤ) : ℚ) + 1 ≤ ⌊t'⌋ := by exact_mod_cast h'
    have a1 := lamOne_lt hf1
    have a2 := lamOne_ge hf0'
    linarith
  · rw [heq]
    have hfr : Int.fract t < Int.fract t' := by
      rw [← Int.self_sub_floor, ← Int.self_sub_floor, heq]
      linarith
    have := lamOne_strictMono hfr
    linarith

theorem lamFun_int_add (k : ℤ) (t : ℚ) : lamFun (k + t) = k + lamFun t := by
  rw [add_comm (k : ℚ) t, lamFun_add_int, add_comm]

theorem lamFun_surjective : Function.Surjective lamFun := by
  intro y
  have hy := Int.floor_add_fract (y - 5 / 18)
  have hr0 := Int.fract_nonneg (y - 5 / 18)
  have hr1 := Int.fract_lt_one (y - 5 / 18)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ⌊y - 5 / 18⌋ = k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℚ, Int.fract (y - 5 / 18) = r := ⟨_, rfl⟩
  rw [hk, hr] at hy
  rw [hr] at hr0 hr1
  rcases le_or_gt r (1 / 18) with h1 | h1
  · refine ⟨k + 6 * r, ?_⟩
    rw [lamFun_int_add, lamFun_of_mem (t := 6 * r) (by linarith) (by linarith),
      lamOne_piece1 (by linarith)]
    linarith
  rcases le_or_gt r (5 / 9) with h2 | h2
  · refine ⟨k + (r + 5 / 18), ?_⟩
    rw [lamFun_int_add, lamFun_of_mem (t := r + 5 / 18) (by linarith) (by linarith),
      lamOne_piece2 (by linarith) (by linarith)]
    linarith
  rcases le_or_gt r (13 / 18) with h3 | h3
  · refine ⟨k + (r + 5 / 18 + 25 / 6) / 6, ?_⟩
    rw [lamFun_int_add, lamFun_of_mem (t := (r + 5 / 18 + 25 / 6) / 6) (by linarith) (by linarith),
      lamOne_piece3 (by linarith) (by linarith)]
    linarith
  · refine ⟨k + (r + 1) / 2, ?_⟩
    rw [lamFun_int_add, lamFun_of_mem (t := (r + 1) / 2) (by linarith) (by linarith),
      lamOne_piece4 (by linarith)]
    linarith

theorem lamFun_bijective : Function.Bijective lamFun :=
  ⟨lamFun_strictMono.injective, lamFun_surjective⟩

/-- **Hyde–Lodha's `f`**, as a permutation of `ℚ`. -/
noncomputable def lamPerm : Equiv.Perm ℚ := Equiv.ofBijective lamFun lamFun_bijective

theorem lamPerm_apply (t : ℚ) : lamPerm t = lamFun t := rfl

/-- `f 0 = 10/36`: `ℤ` is not `f`-invariant. -/
theorem lamPerm_zero : lamPerm 0 = 5 / 18 := by
  rw [lamPerm_apply, lamFun_of_mem le_rfl zero_le_one, lamOne_piece1 (by norm_num)]
  norm_num

theorem lamPerm_add_one (t : ℚ) : lamPerm (t + 1) = lamPerm t + 1 := by
  rw [lamPerm_apply, lamPerm_apply]
  exact_mod_cast lamFun_add_int t 1

/-! ## Grid affinity -/

theorem gridPt_six_two (k : ℤ) : gridPt 6 2 k = (k : ℚ) / 36 := by
  unfold gridPt
  norm_num

/-- The pieces of `f` on the level-`2` grid intervals of `[0, 1]`. -/
theorem lamFun_slope_piece (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r < 36) :
    ∃ s ∈ slopes23, s ∈ Grid 6 3 ∧ (s = 1 / 6 ∨ s = 1 ∨ s = 6 ∨ s = 2) ∧
      AffineOn lamFun (gridPt 6 2 r) (gridPt 6 2 (r + 1)) s := by
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  rw [gridPt_six_two, gridPt_six_two]
  push_cast
  rcases (by omega : r + 1 ≤ 12 ∨ (12 ≤ r ∧ r + 1 ≤ 30) ∨ r = 30 ∨ 31 ≤ r) with h | h | h | h
  · have h' : (r : ℚ) + 1 ≤ 12 := by exact_mod_cast h
    refine ⟨1 / 6, mem_slopes23.mpr ⟨-1, -1, by rw [zpow_neg_one, zpow_neg_one]; norm_num⟩,
      ⟨36, by norm_num⟩, Or.inl rfl, fun t ht1 ht2 => ?_⟩
    rw [lamFun_of_mem (t := t) (by linarith) (by linarith),
      lamFun_of_mem (t := (r : ℚ) / 36) (by linarith) (by linarith),
      lamOne_piece1 (s := t) (by linarith), lamOne_piece1 (s := (r : ℚ) / 36) (by linarith)]
    ring
  · have h1 : (12 : ℚ) ≤ r := by exact_mod_cast h.1
    have h2 : (r : ℚ) + 1 ≤ 30 := by exact_mod_cast h.2
    refine ⟨1, mem_slopes23.mpr ⟨0, 0, by norm_num⟩, ⟨216, by norm_num⟩, Or.inr (Or.inl rfl),
      fun t ht1 ht2 => ?_⟩
    rw [lamFun_of_mem (t := t) (by linarith) (by linarith),
      lamFun_of_mem (t := (r : ℚ) / 36) (by linarith) (by linarith),
      lamOne_piece2 (s := t) (by linarith) (by linarith),
      lamOne_piece2 (s := (r : ℚ) / 36) (by linarith) (by linarith)]
    ring
  · subst h
    refine ⟨6, mem_slopes23.mpr ⟨1, 1, by norm_num⟩, ⟨1296, by norm_num⟩, Or.inr (Or.inr (Or.inl rfl)),
      fun t ht1 ht2 => ?_⟩
    push_cast at ht1 ht2 ⊢
    rw [lamFun_of_mem (t := t) (by linarith) (by linarith),
      lamFun_of_mem (t := (30 : ℚ) / 36) (by norm_num) (by norm_num),
      lamOne_piece3 (s := t) (by linarith) (by linarith),
      lamOne_piece3 (s := (30 : ℚ) / 36) (by norm_num) (by norm_num)]
    ring
  · have h1 : (31 : ℚ) ≤ r := by exact_mod_cast h
    have h2 : (r : ℚ) + 1 ≤ 36 := by exact_mod_cast hr1
    refine ⟨2, mem_slopes23.mpr ⟨1, 0, by norm_num⟩, ⟨432, by norm_num⟩, Or.inr (Or.inr (Or.inr rfl)),
      fun t ht1 ht2 => ?_⟩
    rw [lamFun_of_mem (t := t) (by linarith) (by linarith),
      lamFun_of_mem (t := (r : ℚ) / 36) (by linarith) (by linarith),
      lamOne_piece4 (s := t) (by linarith), lamOne_piece4 (s := (r : ℚ) / 36) (by linarith)]
    ring

/-- The values of `f` at the level-`2` grid points of `[0, 1)`. -/
theorem lamFun_value_piece (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r < 36) :
    lamFun (gridPt 6 2 r) ∈ Grid 6 3 := by
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℚ) + 1 ≤ 36 := by exact_mod_cast hr1
  rw [gridPt_six_two, lamFun_of_mem (t := (r : ℚ) / 36) (by linarith) (by linarith)]
  rcases (by omega : r ≤ 12 ∨ (12 ≤ r ∧ r ≤ 30) ∨ (30 ≤ r ∧ r ≤ 31) ∨ 31 ≤ r) with h | h | h | h
  · have h' : (r : ℚ) ≤ 12 := by exact_mod_cast h
    rw [lamOne_piece1 (by linarith)]
    exact ⟨r + 60, by push_cast; ring⟩
  · have h1 : (12 : ℚ) ≤ r := by exact_mod_cast h.1
    have h2 : (r : ℚ) ≤ 30 := by exact_mod_cast h.2
    rw [lamOne_piece2 (by linarith) (by linarith)]
    exact ⟨6 * r, by push_cast; ring⟩
  · have h1 : (30 : ℚ) ≤ r := by exact_mod_cast h.1
    have h2 : (r : ℚ) ≤ 31 := by exact_mod_cast h.2
    rw [lamOne_piece3 (by linarith) (by linarith)]
    exact ⟨36 * r - 900, by push_cast; ring⟩
  · have h1 : (31 : ℚ) ≤ r := by exact_mod_cast h
    rw [lamOne_piece4 (by linarith)]
    exact ⟨12 * r - 156, by push_cast; ring⟩

theorem lamFun_gridAffine : GridAffine 6 slopes23 lamFun 2 3 :=
  gridAffine_six_of_periodic lamFun_add_int
    (fun r hr0 hr1 => by
      have hr1' : r < 36 := by norm_num at hr1; exact hr1
      obtain ⟨s, hs, hsB, -, haff⟩ := lamFun_slope_piece r hr0 hr1'
      exact ⟨s, hs, hsB, haff⟩)
    (fun r hr0 hr1 => lamFun_value_piece r hr0 (by norm_num at hr1; exact hr1))

/-- Every slope of `f` on a level-`2` grid interval is `1/6`, `1`, `6` or `2`. -/
theorem lamFun_slope_eq (k : ℤ) (s : ℚ)
    (h : AffineOn lamFun (gridPt 6 2 k) (gridPt 6 2 (k + 1)) s) :
    s = 1 / 6 ∨ s = 1 ∨ s = 6 ∨ s = 2 := by
  obtain ⟨r, q, rfl, hr0, hr1⟩ : ∃ r q : ℤ, k = r + q * 36 ∧ 0 ≤ r ∧ r < 36 :=
    ⟨k % 36, k / 36, by rw [mul_comm]; exact (Int.emod_add_mul_ediv k 36).symm,
      Int.emod_nonneg k (by norm_num), Int.emod_lt_of_pos k (by norm_num)⟩
  obtain ⟨s', -, -, hs', haff'⟩ := lamFun_slope_piece r hr0 hr1
  rw [gridPt_six_two, gridPt_six_two] at h haff'
  push_cast at h haff'
  have hb := h (((r : ℚ) + q * 36 + 1) / 36) (by linarith) le_rfl
  have hb' := haff' (((r : ℚ) + 1) / 36) (by linarith) le_rfl
  have e1 : ((r : ℚ) + q * 36 + 1) / 36 = ((r : ℚ) + 1) / 36 + q := by ring
  have e2 : ((r : ℚ) + q * 36) / 36 = (r : ℚ) / 36 + q := by ring
  rw [e1, e2, lamFun_add_int, lamFun_add_int] at hb
  have hss : s = s' := by linear_combination (-36 : ℚ) * hb + 36 * hb'
  rw [hss]
  exact hs'

theorem lamPerm_inv_gridAffine : GridAffine 6 slopes23 ⇑lamPerm⁻¹ 3 (2 + 1 + 3) := by
  have hinv : ∀ k : ℤ, ∀ s : ℚ, AffineOn lamFun (gridPt 6 2 k) (gridPt 6 2 (k + 1)) s →
      s⁻¹ ∈ slopes23 ∧ s⁻¹ ∈ Grid 6 1 := by
    intro k s hs
    rcases lamFun_slope_eq k s hs with rfl | rfl | rfl | rfl
    · exact ⟨mem_slopes23.mpr ⟨1, 1, by norm_num⟩, ⟨36, by norm_num⟩⟩
    · exact ⟨mem_slopes23.mpr ⟨0, 0, by norm_num⟩, ⟨6, by norm_num⟩⟩
    · exact ⟨mem_slopes23.mpr ⟨-1, -1, by rw [zpow_neg_one, zpow_neg_one]; norm_num⟩, ⟨1, by norm_num⟩⟩
    · exact ⟨mem_slopes23.mpr ⟨-1, 0, by rw [zpow_neg_one, zpow_zero]; norm_num⟩, ⟨3, by norm_num⟩⟩
  exact lamFun_gridAffine.inverse lamFun_strictMono (fun x => perm_inv_apply_self lamPerm x)
    (fun y => perm_apply_inv_self lamPerm y) hinv

theorem lamPerm_mem_PLGroup : lamPerm ∈ PLGroup 6 slopes23 :=
  (mem_PLGroup 6 slopes23).mpr ⟨lamFun_strictMono, ⟨2, 3, lamFun_gridAffine⟩,
    ⟨3, 2 + 1 + 3, lamPerm_inv_gridAffine⟩⟩

/-! ## Condition (3) -/

theorem fract_ne_of_not_dyadic6 {x : ℚ} (hx : ¬ Dyadic6 x) {c : ℚ} (hc : c ∈ Grid 6 2) :
    Int.fract x ≠ c := by
  intro h
  apply hx
  refine ⟨2, ?_⟩
  have e : x = ⌊x⌋ + c := by rw [← h, Int.floor_add_fract]
  rw [e]
  exact grid_add (int_mem_grid 2 _) hc

/-- **Condition (3) for `f`.** -/
theorem lamPerm_hlCond : HLCond lamPerm := by
  intro x hx
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hxd : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  have hne0 : Int.fract x ≠ 0 := fract_ne_of_not_dyadic6 hx ⟨0, by norm_num⟩
  have hne1 : Int.fract x ≠ 1 / 3 := fract_ne_of_not_dyadic6 hx ⟨12, by norm_num⟩
  have hne2 : Int.fract x ≠ 5 / 6 := fract_ne_of_not_dyadic6 hx ⟨30, by norm_num⟩
  have hne3 : Int.fract x ≠ 31 / 36 := fract_ne_of_not_dyadic6 hx ⟨31, by norm_num⟩
  have hpos : 0 < Int.fract x := lt_of_le_of_ne hf0 (Ne.symm hne0)
  have hloc : ∀ t : ℚ, (⌊x⌋ : ℚ) ≤ t → t ≤ ⌊x⌋ + 1 →
      lamPerm t = ⌊x⌋ + lamOne (t - ⌊x⌋) := by
    intro t h1 h2
    rw [lamPerm_apply]
    have e := lamFun_add_int (t - ⌊x⌋) ⌊x⌋
    rw [sub_add_cancel] at e
    rw [e, lamFun_of_mem (t := t - ⌊x⌋) (by linarith) (by linarith)]
    ring
  have hlocx : lamPerm x = ⌊x⌋ + lamOne (Int.fract x) := by
    rw [hloc x (Int.floor_le x) (Int.lt_floor_add_one x).le, Int.self_sub_floor]
  rcases lt_or_gt_of_ne hne1 with h1 | h1
  · refine ⟨⌊x⌋ + Int.fract x / 2, ⌊x⌋ + (Int.fract x + 1 / 3) / 2, -1, -1, by linarith,
      by linarith, fun t ht1 ht2 => ?_, ?_⟩
    · rw [hloc t (by linarith) (by linarith),
        hloc (⌊x⌋ + Int.fract x / 2) (by linarith) (by linarith),
        lamOne_piece1 (s := t - ⌊x⌋) (by linarith),
        lamOne_piece1 (s := ⌊x⌋ + Int.fract x / 2 - ⌊x⌋) (by linarith),
        zpow_neg_one, zpow_neg_one]
      ring
    · have hfl : ⌊lamPerm x⌋ = ⌊x⌋ := by
        have hz : ⌊Int.fract x / 6 + 5 / 18⌋ = 0 :=
          Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        rw [hlocx, lamOne_piece1 h1.le, Int.floor_intCast_add, hz, add_zero]
      rw [hfl]
      omega
  rcases lt_or_gt_of_ne hne2 with h2 | h2
  · refine ⟨⌊x⌋ + (Int.fract x + 1 / 3) / 2, ⌊x⌋ + (Int.fract x + 5 / 6) / 2, 0, 0, by linarith,
      by linarith, fun t ht1 ht2 => ?_, ?_⟩
    · rw [hloc t (by linarith) (by linarith),
        hloc (⌊x⌋ + (Int.fract x + 1 / 3) / 2) (by linarith) (by linarith),
        lamOne_piece2 (s := t - ⌊x⌋) (by linarith) (by linarith),
        lamOne_piece2 (s := ⌊x⌋ + (Int.fract x + 1 / 3) / 2 - ⌊x⌋) (by linarith) (by linarith),
        zpow_zero, zpow_zero]
      ring
    · have hfl : ⌊lamPerm x⌋ = ⌊x⌋ := by
        have hz : ⌊Int.fract x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        rw [hlocx, lamOne_piece2 h1.le h2.le, Int.floor_intCast_add, hz, add_zero]
      rw [hfl]
      omega
  rcases lt_or_gt_of_ne hne3 with h3 | h3
  · refine ⟨⌊x⌋ + (Int.fract x + 5 / 6) / 2, ⌊x⌋ + (Int.fract x + 31 / 36) / 2, 1, 1, by linarith,
      by linarith, fun t ht1 ht2 => ?_, ?_⟩
    · rw [hloc t (by linarith) (by linarith),
        hloc (⌊x⌋ + (Int.fract x + 5 / 6) / 2) (by linarith) (by linarith),
        lamOne_piece3 (s := t - ⌊x⌋) (by linarith) (by linarith),
        lamOne_piece3 (s := ⌊x⌋ + (Int.fract x + 5 / 6) / 2 - ⌊x⌋) (by linarith) (by linarith),
        zpow_one, zpow_one]
      ring
    · have hfl : ⌊lamPerm x⌋ = ⌊x⌋ := by
        have hz : ⌊6 * Int.fract x - 25 / 6⌋ = 0 :=
          Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
        rw [hlocx, lamOne_piece3 h2.le h3.le, Int.floor_intCast_add, hz, add_zero]
      rw [hfl]
      omega
  · refine ⟨⌊x⌋ + (Int.fract x + 31 / 36) / 2, ⌊x⌋ + (Int.fract x + 1) / 2, 1, 0, by linarith,
      by linarith, fun t ht1 ht2 => ?_, ?_⟩
    · rw [hloc t (by linarith) (by linarith),
        hloc (⌊x⌋ + (Int.fract x + 31 / 36) / 2) (by linarith) (by linarith),
        lamOne_piece4 (s := t - ⌊x⌋) (by linarith),
        lamOne_piece4 (s := ⌊x⌋ + (Int.fract x + 31 / 36) / 2 - ⌊x⌋) (by linarith),
        zpow_one, zpow_zero]
      ring
    · have hone : ⌊2 * Int.fract x - 13 / 18⌋ = 1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have hfl : ⌊lamPerm x⌋ = ⌊x⌋ + 1 := by
        rw [hlocx, lamOne_piece4 h3.le, Int.floor_intCast_add, hone]
      rw [hfl]
      omega

/-- **`f ∈ Γ₂`** (Hyde–Lodha, proof of Proposition 3.4: "Clearly, `f ∈ Γ_n`"). -/
theorem lamPerm_mem_gammaTwo : lamPerm ∈ gammaTwo :=
  mem_gammaTwo.mpr ⟨lamPerm_mem_PLGroup, lamPerm_add_one, lamPerm_hlCond⟩

/-- **`ℤ` is not `f`-invariant**: `f 0 ∉ ℤ`. -/
theorem lamPerm_zero_not_int : ∀ k : ℤ, lamPerm 0 ≠ k := by
  intro k hk
  rw [lamPerm_zero] at hk
  have h1 : (0 : ℚ) < k := by linarith
  have h2 : (k : ℚ) < 1 := by linarith
  have h1' : (0 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < 1 := by exact_mod_cast h2
  omega

#audit_axioms GroupApproximation.HydeLodha.gridAffine_six_of_periodic
#audit_axioms GroupApproximation.HydeLodha.lamPerm_mem_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.lamPerm_zero
#audit_axioms GroupApproximation.HydeLodha.lamPerm_zero_not_int

end HydeLodha
end GroupApproximation
