import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationSlopes
import GroupApproximation.GroupTheory.HydeLodha.PeriodicDisplacement
import GroupApproximation.Meta.AxiomGuard

/-!
# Germs of elements of `Γ₂` at a fixed grid point

Tools for Hyde–Lodha, Lemma 4.5, second case (`b = a + 1`), in the unit frame `0 < a < 1`:

* `exists_germLeft_of_fix`: an element of `Γ₂` fixing `a` is `t ↦ a + 6^i (t - a)` just right of `a`
  (condition (3) at a point outside `ℤ[1/6]` between `a` and the next grid point forces
  `i - j = 0` for its slope `2^i 3^j`);
* `germLeft_pow`, `germLeft_zpow`: powers of an element with germ `6` at `a⁺`;
* `germLeft_iterate_ge`: `a + min (6^n s) λ ≤ f^n (a + s)` for such an element;
* `supportedIn_of_germLeft_zero`: an element of `Γ₂` that is the identity on `[a, a + ε]` is
  supported in `(a + ε, a + 1) + ℤ`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem exists_gridPt_eq {x : ℚ} {M L : ℕ} (hx : x ∈ Grid 6 M) (hML : M ≤ L) :
    ∃ k : ℤ, gridPt 6 L k = x := by
  obtain ⟨k, hk⟩ := grid_mono (m := 6) hML hx
  refine ⟨k, ?_⟩
  have h6 : ((6 : ℕ) : ℚ) ^ L ≠ 0 := pow_ne_zero L (by norm_num)
  unfold gridPt
  rw [div_eq_iff h6, hk]

theorem gridPt_six_succ (L : ℕ) (k : ℤ) : gridPt 6 L (k + 1) = gridPt 6 L k + ((6 : ℚ) ^ L)⁻¹ := by
  unfold gridPt
  push_cast
  rw [add_div, one_div]

/-- **The germ at a fixed grid point.** -/
theorem exists_germLeft_of_fix {k : Equiv.Perm ℚ} (hk : k ∈ gammaTwo) {a : ℚ}
    (ha : ∃ M, a ∈ Grid 6 M) (h0a : 0 < a) (ha1 : a < 1) (hka : k a = a) :
    ∃ i : ℤ, ∃ ε : ℚ, GermLeft 4 a i ε k := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, hc⟩ := mem_gammaTwo.mp hk
  obtain ⟨Ma, hMa⟩ := ha
  obtain ⟨k₀, hk₀⟩ := exists_gridPt_eq hMa (le_max_right N Ma)
  obtain ⟨s, ⟨i, j, hsij⟩, -, haff⟩ := hA.affine_fine (le_max_left N Ma) k₀
  rw [gridPt_six_succ, hk₀] at haff
  have hs : 0 < s := by
    rw [hsij]
    exact mul_pos (zpow_pos (by norm_num) i) (zpow_pos (by norm_num) j)
  have hX0 : (0 : ℚ) < ((6 : ℚ) ^ (max N Ma))⁻¹ := by positivity
  obtain ⟨L', hLL', hL'⟩ := exists_level (m := 4) (max N Ma)
    (δ := min (min ((1 - a) / 2 * s⁻¹) ((6 : ℚ) ^ (max N Ma))⁻¹) ((1 - a) / 2))
    (lt_min (lt_min (mul_pos (by linarith) (inv_pos.mpr hs)) hX0) (by linarith))
  rw [six_cast] at hL'
  have hL1 : ((6 : ℚ) ^ L')⁻¹ ≤ (1 - a) / 2 * s⁻¹ := le_trans hL' (le_trans (min_le_left _ _)
    (min_le_left _ _))
  have hL2 : ((6 : ℚ) ^ L')⁻¹ ≤ ((6 : ℚ) ^ (max N Ma))⁻¹ := le_trans hL' (le_trans
    (min_le_left _ _) (min_le_right _ _))
  have hL3 : ((6 : ℚ) ^ L')⁻¹ ≤ (1 - a) / 2 := le_trans hL' (min_le_right _ _)
  obtain ⟨k₁, hk₁⟩ := exists_gridPt_eq hMa (le_trans (le_max_right N Ma) hLL')
  have hnd := not_dyadic6_gridPt_add_fifth L' k₁
  rw [hk₁] at hnd
  have h6 : (0 : ℚ) < 6 ^ L' := pow_pos (by norm_num) L'
  have hX5 : ((5 : ℚ) * 6 ^ L')⁻¹ < ((6 : ℚ) ^ L')⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) h6]
    linarith
  have hX5pos : (0 : ℚ) < ((5 : ℚ) * 6 ^ L')⁻¹ := by positivity
  obtain ⟨a₀, b₀, i', j', hax, hxb, haff', hij⟩ := hc _ hnd
  have hkx := haff (a + ((5 : ℚ) * 6 ^ L')⁻¹) (by linarith) (by linarith)
  rw [hka] at hkx
  have hsX : s * ((5 : ℚ) * 6 ^ L')⁻¹ ≤ (1 - a) / 2 := by
    have h1 : s * ((5 : ℚ) * 6 ^ L')⁻¹ ≤ s * ((1 - a) / 2 * s⁻¹) :=
      mul_le_mul_of_nonneg_left (by linarith) hs.le
    have e : s * ((1 - a) / 2 * s⁻¹) = (1 - a) / 2 := by
      rw [mul_comm s, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
    linarith
  have hsXpos : 0 < s * ((5 : ℚ) * 6 ^ L')⁻¹ := mul_pos hs hX5pos
  have hfl1 : ⌊k (a + ((5 : ℚ) * 6 ^ L')⁻¹)⌋ = 0 := by
    rw [hkx, Int.floor_eq_zero_iff]
    constructor <;> nlinarith
  have hfl2 : ⌊a + ((5 : ℚ) * 6 ^ L')⁻¹⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor <;> linarith
  rw [hfl1, hfl2, sub_self] at hij
  have hji : j' = i' := by omega
  have hseq : s = (2 : ℚ) ^ i' * (3 : ℚ) ^ j' :=
    affineOn_slope_eq haff haff' (by linarith) (by linarith) hax hxb
  refine ⟨i', ((6 : ℚ) ^ (max N Ma))⁻¹, ?_⟩
  unfold GermLeft
  refine ⟨hX0, fun t h1 h2 => ?_⟩
  rw [haff t h1 h2, hka, hseq, hji, ← mul_zpow]
  norm_num

/-! ## Powers -/

theorem germLeft_pow {a ε : ℚ} {f : Equiv.Perm ℚ} (hf : GermLeft 4 a 1 ε f) (n : ℕ) :
    ∃ ε' : ℚ, GermLeft 4 a (n : ℤ) ε' (f ^ n) := by
  induction n with
  | zero =>
    refine ⟨1, ?_⟩
    unfold GermLeft
    refine ⟨one_pos, fun t _ _ => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨ε', h⟩ := ih
    have e : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    exact ⟨_, by rw [pow_succ', e]; exact hf.mul h⟩

theorem germLeft_zpow {a ε : ℚ} {f : Equiv.Perm ℚ} (hf : GermLeft 4 a 1 ε f) (n : ℤ) :
    ∃ ε' : ℚ, GermLeft 4 a n ε' (f ^ n) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨ε', h⟩ := germLeft_pow hf m
    exact ⟨ε', by rw [zpow_natCast]; exact h⟩
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    obtain ⟨ε', h⟩ := germLeft_pow hf m
    exact ⟨_, by rw [zpow_neg, zpow_natCast]; exact h.inv⟩

theorem germLeft_iterate_ge {a ε lam : ℚ} {f : Equiv.Perm ℚ} (hf : GermLeft 4 a 1 ε f)
    (hmono : StrictMono f) (hlam0 : 0 ≤ lam) (hlam : lam ≤ ε) {s : ℚ} (hs : 0 ≤ s) (n : ℕ) :
    a + min ((6 : ℚ) ^ n * s) lam ≤ (f ^ n) (a + s) := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Equiv.Perm.one_apply]
    linarith [min_le_left s lam]
  | succ n ih =>
    rw [pow_succ' f n, Equiv.Perm.mul_apply]
    have hm0 : 0 ≤ min ((6 : ℚ) ^ n * s) lam := le_min (by positivity) hlam0
    have hm1 : min ((6 : ℚ) ^ n * s) lam ≤ lam := min_le_right _ _
    have h1 := hmono.monotone ih
    have h2 : f (a + min ((6 : ℚ) ^ n * s) lam) = a + 6 * min ((6 : ℚ) ^ n * s) lam := by
      rw [hf.2 _ (by linarith) (by linarith), zpow_one, six_cast]
      ring
    rw [h2] at h1
    have h3 : min ((6 : ℚ) ^ (n + 1) * s) lam ≤ 6 * min ((6 : ℚ) ^ n * s) lam := by
      rcases min_cases ((6 : ℚ) ^ n * s) lam with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        exact (min_le_left _ _).trans (le_of_eq (by ring))
      · rw [h]
        exact (min_le_right _ _).trans (by linarith)
    linarith

/-! ## Trivial germ -/

theorem supportedIn_of_germLeft_zero {k : Equiv.Perm ℚ} (hk : k ∈ gammaTwo) {a ε : ℚ}
    (hk0 : GermLeft 4 a 0 ε k) : SupportedIn k (perIoo (a + ε) (a + 1)) := by
  intro t ht
  obtain ⟨j, hj⟩ : ∃ j : ℤ, ⌊t - a⌋ = j := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℚ, Int.fract (t - a) = r := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [← hr]; exact Int.fract_nonneg _
  have hr1 : r < 1 := by rw [← hr]; exact Int.fract_lt_one _
  have hdec : t = (a + r) + j := by
    have e := Int.floor_add_fract (t - a)
    rw [hj, hr] at e
    linarith
  have hrε : r ≤ ε := by
    by_contra hc
    have hc' := not_le.mp hc
    apply ht
    refine ⟨-j, ?_, ?_⟩ <;> push_cast <;> linarith
  rw [hdec, gammaTwo_add_int hk, germLeft_zero_fix (m := 4) (t := a + r) hk0 (by linarith)
    (by linarith)]

#audit_axioms GroupApproximation.HydeLodha.exists_germLeft_of_fix
#audit_axioms GroupApproximation.HydeLodha.germLeft_zpow
#audit_axioms GroupApproximation.HydeLodha.germLeft_iterate_ge
#audit_axioms GroupApproximation.HydeLodha.supportedIn_of_germLeft_zero

end HydeLodha
end GroupApproximation
