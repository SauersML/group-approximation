import GroupApproximation.GroupTheory.HydeLodha.PeriodicCore
import GroupApproximation.GroupTheory.HydeLodha.GammaTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# The stabilizer of `0` in `Γ₂` is the periodic `F_6`

Hyde–Lodha, Proposition 1.4(2): "Any element `f ∈ Γ_n` that fixes `0` must pointwise fix `ℤ`, due to
condition (2) of Definition 1.2.  Indeed, it follows from Definition 1.2 that `f` is an element in
the `1`-periodic action of `F_{η_n}`."  For `n = 2`, `η = 6 = 4 + 2`:

* `gammaTwo_apply_int_of_fix_zero`, `floor_apply_of_fix_zero`: `f` fixes `ℤ` and preserves `⌊·⌋`;
* `gridAffine_powSlopes_of_fix_zero`: every slope of `f` is a power of `6`, because condition (3) at a
  point `x ∉ ℤ[1/6]` of a grid interval gives a slope `2^i 3^j` with `i - j = ⌊f x⌋ - ⌊x⌋ = 0`
  (`not_dyadic6_gridPt_add_fifth` supplies the point, `affineOn_slope_eq` identifies the slopes);
* `unitPartPerm`: `f` on `[0, 1]`, the identity elsewhere, an element of `F_{6,1}` (glued at `0`, `1`);
* `mem_range_perHom_of_fix_zero`: `f = perHom 4 (unitPartPerm f)`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-! ## A point outside `ℤ[1/6]` in every grid interval -/

theorem not_dyadic6_gridPt_add_fifth (N : ℕ) (k : ℤ) :
    ¬ Dyadic6 (gridPt 6 N k + ((5 : ℚ) * 6 ^ N)⁻¹) := by
  rintro ⟨M, j, hj⟩
  have h6 : (6 : ℚ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have hg : gridPt 6 N k * (6 : ℚ) ^ N = k := by
    unfold gridPt
    push_cast
    exact div_mul_cancel₀ _ h6
  have hinv : ((5 : ℚ) * 6 ^ N)⁻¹ * (5 * 6 ^ N) = 1 := inv_mul_cancel₀ (by positivity)
  push_cast at hj
  have hQ : (5 * (k : ℚ) + 1) * (6 : ℚ) ^ M = 5 * (j : ℚ) * (6 : ℚ) ^ N := by
    linear_combination (5 * (6 : ℚ) ^ N) * hj - 5 * (6 : ℚ) ^ M * hg - (6 : ℚ) ^ M * hinv
  have hZ : (5 * k + 1) * 6 ^ M = 5 * j * 6 ^ N := by exact_mod_cast hQ
  have hp : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_five
  have hdvd : (5 : ℤ) ∣ (5 * k + 1) * 6 ^ M := ⟨j * 6 ^ N, by rw [hZ]; ring⟩
  rcases hp.dvd_or_dvd hdvd with h | h
  · omega
  · have h6' := hp.dvd_of_dvd_pow h
    omega

/-- Two affine pieces through a common interior point have the same slope. -/
theorem affineOn_slope_eq {f : ℚ → ℚ} {a b a' b' s s' x : ℚ} (h : AffineOn f a b s)
    (h' : AffineOn f a' b' s') (hax : a < x) (hxb : x < b) (ha'x : a' < x) (hxb' : x < b') :
    s = s' := by
  have hu : max a a' < min b b' := lt_of_lt_of_le (max_lt hax ha'x) (le_min hxb.le hxb'.le)
  have h1 := h (min b b') (le_trans (le_max_left a a') hu.le) (min_le_left b b')
  have h2 := h (max a a') (le_max_left a a') (le_trans hu.le (min_le_left b b'))
  have h3 := h' (min b b') (le_trans (le_max_right a a') hu.le) (min_le_right b b')
  have h4 := h' (max a a') (le_max_right a a') (le_trans hu.le (min_le_right b b'))
  have hd : (min b b' - max a a') ≠ 0 := (sub_pos.mpr hu).ne'
  have e : (s - s') * (min b b' - max a a') = 0 := by linear_combination h1 - h2 - h3 + h4
  rcases mul_eq_zero.mp e with e | e
  · linarith
  · exact absurd e hd

/-! ## Elements of `Γ₂` fixing `0` -/

section Fix

variable {f : Equiv.Perm ℚ}

theorem gammaTwo_apply_int_of_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) (k : ℤ) :
    f k = k := by
  have h := gammaTwo_add_int hf 0 k
  rwa [zero_add, h0, zero_add] at h

theorem gammaTwo_strictMono (hf : f ∈ gammaTwo) : StrictMono f :=
  (mem_gammaTwo.mp hf).1.1

theorem floor_apply_of_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) (x : ℚ) : ⌊f x⌋ = ⌊x⌋ := by
  have hmono := gammaTwo_strictMono hf
  rw [Int.floor_eq_iff]
  constructor
  · have h := hmono.monotone (Int.floor_le x)
    rwa [gammaTwo_apply_int_of_fix_zero hf h0] at h
  · have h := hmono (Int.lt_floor_add_one x)
    have e : ((⌊x⌋ : ℤ) : ℚ) + 1 = ((⌊x⌋ + 1 : ℤ) : ℚ) := by push_cast; ring
    rw [e, gammaTwo_apply_int_of_fix_zero hf h0] at h
    push_cast at h
    exact h

theorem six_zpow_eq_powSlopes (i : ℤ) : (2 : ℚ) ^ i * (3 : ℚ) ^ i ∈ powSlopes 4 := by
  refine ⟨i, ?_⟩
  rw [← mul_zpow]
  norm_num

/-- **The slopes of an element of `Γ₂` fixing `0` are powers of `6`.** -/
theorem gridAffine_powSlopes_of_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) {N B : ℕ}
    (hA : GridAffine 6 slopes23 f N B) : GridAffine 6 (powSlopes 4) f N B := by
  obtain ⟨-, -, hc⟩ := mem_gammaTwo.mp hf
  refine ⟨fun k => ?_, hA.value⟩
  obtain ⟨s, -, hsB, haff⟩ := hA.slope k
  refine ⟨s, ?_, hsB, haff⟩
  have h6 : (0 : ℚ) < 6 ^ N := pow_pos (by norm_num) N
  have hstep : gridPt 6 N (k + 1) = gridPt 6 N k + ((6 : ℚ) ^ N)⁻¹ := by
    unfold gridPt
    push_cast
    rw [add_div, one_div]
  have hlt : ((5 : ℚ) * 6 ^ N)⁻¹ < ((6 : ℚ) ^ N)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) h6]
    linarith
  have hposx : (0 : ℚ) < ((5 : ℚ) * 6 ^ N)⁻¹ := by positivity
  obtain ⟨a, b, i, j, hax, hxb, haff', hij⟩ := hc _ (not_dyadic6_gridPt_add_fifth N k)
  have hs : s = (2 : ℚ) ^ i * (3 : ℚ) ^ j :=
    affineOn_slope_eq haff haff' (by linarith) (by rw [hstep]; linarith) hax hxb
  rw [floor_apply_of_fix_zero hf h0, sub_self] at hij
  have hji : j = i := by omega
  rw [hs, hji]
  exact six_zpow_eq_powSlopes i

theorem inv_mem_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) : f⁻¹ ∈ gammaTwo ∧ f⁻¹ 0 = 0 :=
  ⟨gammaTwo.inv_mem hf, by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩

theorem apply_mem_unit_of_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) {t : ℚ} (h0t : 0 ≤ t)
    (h1t : t ≤ 1) : 0 ≤ f t ∧ f t ≤ 1 := by
  have hmono := gammaTwo_strictMono hf
  have h1 : f 1 = 1 := by exact_mod_cast gammaTwo_apply_int_of_fix_zero hf h0 1
  constructor
  · have h := hmono.monotone h0t
    rwa [h0] at h
  · have h := hmono.monotone h1t
    rwa [h1] at h

/-! ## The restriction to `[0, 1]` -/

/-- `f` on `[0, 1]`, the identity elsewhere. -/
def unitPart (f : Equiv.Perm ℚ) (t : ℚ) : ℚ := if 0 ≤ t ∧ t ≤ 1 then f t else t

theorem unitPart_of_mem {t : ℚ} (h0t : 0 ≤ t) (h1t : t ≤ 1) : unitPart f t = f t := by
  simp only [unitPart, if_pos (And.intro h0t h1t)]

theorem unitPart_of_not_mem {t : ℚ} (ht : ¬ (0 ≤ t ∧ t ≤ 1)) : unitPart f t = t := by
  simp only [unitPart, if_neg ht]

theorem unitPart_left_inv (hf : f ∈ gammaTwo) (h0 : f 0 = 0) (t : ℚ) :
    unitPart f⁻¹ (unitPart f t) = t := by
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · have hm := apply_mem_unit_of_fix_zero hf h0 ht.1 ht.2
    rw [unitPart_of_mem ht.1 ht.2, unitPart_of_mem hm.1 hm.2, perm_inv_apply_self]
  · rw [unitPart_of_not_mem ht, unitPart_of_not_mem ht]

theorem unitPart_right_inv (hf : f ∈ gammaTwo) (h0 : f 0 = 0) (t : ℚ) :
    unitPart f (unitPart f⁻¹ t) = t := by
  obtain ⟨hfi, hfi0⟩ := inv_mem_fix_zero hf h0
  have h := unitPart_left_inv hfi hfi0 t
  rwa [inv_inv] at h

/-- The restriction as a permutation. -/
def unitPartPerm (hf : f ∈ gammaTwo) (h0 : f 0 = 0) : Equiv.Perm ℚ where
  toFun := unitPart f
  invFun := unitPart f⁻¹
  left_inv := unitPart_left_inv hf h0
  right_inv := unitPart_right_inv hf h0

theorem unitPart_strictMono (hf : f ∈ gammaTwo) (h0 : f 0 = 0) : StrictMono (unitPart f) := by
  have hmono := gammaTwo_strictMono hf
  intro s t hst
  by_cases hs : 0 ≤ s ∧ s ≤ 1
  · by_cases ht : 0 ≤ t ∧ t ≤ 1
    · rw [unitPart_of_mem hs.1 hs.2, unitPart_of_mem ht.1 ht.2]
      exact hmono hst
    · have hm := apply_mem_unit_of_fix_zero hf h0 hs.1 hs.2
      rw [unitPart_of_mem hs.1 hs.2, unitPart_of_not_mem ht]
      have ht1 : 1 < t := by
        by_contra h
        exact ht ⟨by linarith [hs.1], not_lt.mp h⟩
      linarith [hm.2]
  · by_cases ht : 0 ≤ t ∧ t ≤ 1
    · have hm := apply_mem_unit_of_fix_zero hf h0 ht.1 ht.2
      rw [unitPart_of_not_mem hs, unitPart_of_mem ht.1 ht.2]
      have hs0 : s < 0 := by
        by_contra h
        exact hs ⟨not_lt.mp h, by linarith [ht.2]⟩
      linarith [hm.1]
    · rw [unitPart_of_not_mem hs, unitPart_of_not_mem ht]
      exact hst

/-- Grid affinity of the restriction, glued from `id`, `f`, `id` at the grid points `0` and `1`. -/
theorem unitPart_gridAffine (hf : f ∈ gammaTwo) (h0 : f 0 = 0) {N B : ℕ}
    (hA : GridAffine 6 slopes23 f N B) : GridAffine 6 (powSlopes 4) (unitPart f) N (B + N) := by
  have hfA : GridAffine 6 (powSlopes 4) f N (B + N) :=
    (gridAffine_powSlopes_of_fix_zero hf h0 hA).mono_bound (Nat.le_add_right B N)
  have hid : GridAffine 6 (powSlopes 4) id N (B + N) :=
    (gridAffine_id.mono_level (Nat.zero_le N)).mono_bound (by omega)
  have h1 : f 1 = 1 := by exact_mod_cast gammaTwo_apply_int_of_fix_zero hf h0 1
  have hp1 : (1 : ℚ) ∈ Grid 6 N := by simpa using int_mem_grid (m := 6) N 1
  have hp0 : (0 : ℚ) ∈ Grid 6 N := by simpa using int_mem_grid (m := 6) N 0
  have hF₁ : GridAffine 6 (powSlopes 4) (fun t => if t ≤ 1 then f t else t) N (B + N) := by
    refine GridAffine.glue hfA hid hp1 (fun t ht => ?_) (fun t ht => ?_)
    · simp only [if_pos ht]
    · rcases lt_or_eq_of_le ht with ht | rfl
      · simp only [if_neg (not_le.mpr ht), id_eq]
      · simp only [le_refl, if_true, h1, id_eq]
  refine GridAffine.glue hid hF₁ hp0 (fun t ht => ?_) (fun t ht => ?_)
  · rcases lt_or_eq_of_le ht with ht | rfl
    · rw [unitPart_of_not_mem (fun h => absurd h.1 (not_le.mpr ht))]
      rfl
    · rw [unitPart_of_mem le_rfl zero_le_one, h0]
      rfl
  · by_cases ht1 : t ≤ 1
    · rw [unitPart_of_mem ht ht1]
      simp only [if_pos ht1]
    · rw [unitPart_of_not_mem (fun h => ht1 h.2)]
      simp only [if_neg ht1]

theorem unitPartPerm_mem_compactF (hf : f ∈ gammaTwo) (h0 : f 0 = 0) :
    unitPartPerm hf h0 ∈ compactF 4 1 := by
  obtain ⟨hfi, hfi0⟩ := inv_mem_fix_zero hf h0
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, -⟩ := mem_gammaTwo.mp hf
  obtain ⟨⟨-, ⟨Ni, Bi, hAi⟩, -⟩, -, -⟩ := mem_gammaTwo.mp hfi
  show unitPartPerm hf h0 ∈ PLGroup (4 + 2) (powSlopes 4) ∧
    (∀ t : ℚ, t ≤ 0 → unitPartPerm hf h0 t = t) ∧
    ∀ t : ℚ, ((1 : ℕ) : ℚ) ≤ t → unitPartPerm hf h0 t = t
  refine ⟨(mem_PLGroup (4 + 2) (powSlopes 4)).mpr ⟨unitPart_strictMono hf h0,
    ⟨N, B + N, unitPart_gridAffine hf h0 hA⟩, ⟨Ni, Bi + Ni, ?_⟩⟩, fun t ht => ?_, fun t ht => ?_⟩
  · exact unitPart_gridAffine hfi hfi0 hAi
  · show unitPart f t = t
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact unitPart_of_not_mem (fun h => absurd h.1 (not_le.mpr ht))
    · rw [unitPart_of_mem le_rfl zero_le_one, h0]
  · show unitPart f t = t
    rw [Nat.cast_one] at ht
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact unitPart_of_not_mem (fun h => absurd h.2 (not_le.mpr ht))
    · rw [unitPart_of_mem zero_le_one le_rfl]
      exact_mod_cast gammaTwo_apply_int_of_fix_zero hf h0 1

/-- **Hyde–Lodha, Proposition 1.4(2).**  An element of `Γ₂` fixing `0` is in the `1`-periodic copy of
`F_6`. -/
theorem mem_range_perHom_of_fix_zero (hf : f ∈ gammaTwo) (h0 : f 0 = 0) :
    ∃ a : ↥(compactF 4 1), perHom 4 a = f := by
  refine ⟨⟨unitPartPerm hf h0, unitPartPerm_mem_compactF hf h0⟩, ?_⟩
  ext t
  rw [perHom_apply]
  show (⌊t⌋ : ℚ) + unitPart f (Int.fract t) = f t
  rw [unitPart_of_mem (Int.fract_nonneg t) (Int.fract_lt_one t).le]
  have h := gammaTwo_add_int hf (Int.fract t) ⌊t⌋
  rw [Int.fract_add_floor] at h
  rw [h]
  ring

end Fix

#audit_axioms GroupApproximation.HydeLodha.not_dyadic6_gridPt_add_fifth
#audit_axioms GroupApproximation.HydeLodha.gridAffine_powSlopes_of_fix_zero
#audit_axioms GroupApproximation.HydeLodha.unitPartPerm_mem_compactF
#audit_axioms GroupApproximation.HydeLodha.mem_range_perHom_of_fix_zero

end HydeLodha
end GroupApproximation
