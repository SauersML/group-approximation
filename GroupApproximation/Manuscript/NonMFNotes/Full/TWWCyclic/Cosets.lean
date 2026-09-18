import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SolvableInduction

/-!
# Coset combinatorics of a normalizing element of finite order modulo a subgroup

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), finite-index half of the cyclic extension step
(Ozawa--Rørdam--Sato, GAFA 25 (2015), §3: induction from a finite-index
normal subgroup).

Let `k` normalize `H`, and let `m > 0` be least with `k ^ m ∈ H`. The powers
`k ^ 0, …, k ^ (m - 1)` are coset representatives of `H` in `H ⊔ ⟨k⟩`. The
induced representation of an element `x` has the block `x`-coordinates
`cc k x i j = (k ^ i)⁻¹ * x * k ^ j` (with `i, j < m`). A block is used exactly
when `cc k x i j ∈ H`, and this file proves that in every row and every column
exactly one block is used.
-/

namespace GroupApproximation.Full.TWWCyclic

variable {G : Type} [Group G]

/-- The `(i, j)` coset coordinate of `x` for the representatives `k ^ i`. -/
def cc (k x : G) (i j : ℕ) : G := (k ^ i)⁻¹ * x * k ^ j

theorem cc_mul (k x y : G) (i l j : ℕ) : cc k x i l * cc k y l j = cc k (x * y) i j := by
  simp only [cc, mul_assoc, mul_inv_cancel_left]

theorem cc_inv (k x : G) (i j : ℕ) : (cc k x i j)⁻¹ = cc k x⁻¹ j i := by
  simp only [cc, mul_inv_rev, inv_inv, mul_assoc]

theorem cc_one_self (k : G) (i : ℕ) : cc k 1 i i = 1 := by
  simp only [cc, mul_one, inv_mul_cancel]

theorem cc_self_ne_one (k : G) {x : G} (hx : x ≠ 1) (i : ℕ) : cc k x i i ≠ 1 := by
  intro h
  apply hx
  calc x = k ^ i * cc k x i i * (k ^ i)⁻¹ := by
        simp only [cc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

/-! ## Conjugation by powers -/

section Normalizing

variable {H : Subgroup G} {k : G}

theorem conj_pow_mem (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) :
    ∀ n : ℕ, ∀ h ∈ H, k ^ n * h * (k ^ n)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero =>
    intro h hh
    rwa [pow_zero, inv_one, one_mul, mul_one]
  | succ n ih =>
    intro h hh
    have heq : k ^ (n + 1) * h * (k ^ (n + 1))⁻¹ = k ^ n * (k * h * k⁻¹) * (k ^ n)⁻¹ := by
      simp only [pow_succ, mul_inv_rev, mul_assoc]
    rw [heq]
    exact ih _ (hk h hh)

theorem conj_pow_mem' (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) :
    ∀ n : ℕ, ∀ h ∈ H, (k ^ n)⁻¹ * h * k ^ n ∈ H := by
  intro n
  induction n with
  | zero =>
    intro h hh
    rwa [pow_zero, inv_one, one_mul, mul_one]
  | succ n ih =>
    intro h hh
    have heq : (k ^ (n + 1))⁻¹ * h * k ^ (n + 1) = (k ^ n)⁻¹ * (k⁻¹ * h * k) * k ^ n := by
      simp only [pow_succ', mul_inv_rev, mul_assoc]
    rw [heq]
    exact ih _ (hk' h hh)

theorem conj_zpow_mem (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H)
    (n : ℤ) (h : G) (hh : h ∈ H) : k ^ n * h * (k ^ n)⁻¹ ∈ H := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    exact conj_pow_mem hk a h hh
  · rw [zpow_neg, zpow_natCast, inv_inv]
    exact conj_pow_mem' hk' a h hh

/-- `H · ⟨k⟩` as a subgroup, when `k` normalizes `H`. -/
def prodSubgroup (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) :
    Subgroup G where
  carrier := {x | ∃ h ∈ H, ∃ n : ℤ, x = h * k ^ n}
  mul_mem' := by
    rintro _ _ ⟨h₁, hh₁, n₁, rfl⟩ ⟨h₂, hh₂, n₂, rfl⟩
    show ∃ h ∈ H, ∃ n : ℤ, h₁ * k ^ n₁ * (h₂ * k ^ n₂) = h * k ^ n
    refine ⟨h₁ * (k ^ n₁ * h₂ * (k ^ n₁)⁻¹),
      H.mul_mem hh₁ (conj_zpow_mem hk hk' n₁ h₂ hh₂), n₁ + n₂, ?_⟩
    rw [zpow_add]
    simp only [mul_assoc, inv_mul_cancel_left]
  one_mem' := by
    show ∃ h ∈ H, ∃ n : ℤ, (1 : G) = h * k ^ n
    exact ⟨1, H.one_mem, 0, by rw [zpow_zero, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨h, hh, n, rfl⟩
    show ∃ h' ∈ H, ∃ n' : ℤ, (h * k ^ n)⁻¹ = h' * k ^ n'
    refine ⟨k ^ (-n) * h⁻¹ * (k ^ (-n))⁻¹,
      conj_zpow_mem hk hk' (-n) _ (H.inv_mem hh), -n, ?_⟩
    rw [inv_mul_cancel_right, mul_inv_rev, zpow_neg]

/-- Every element of `H ⊔ ⟨k⟩` has the form `h * k ^ n`. -/
theorem exists_mul_zpow_of_mem_sup (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {x : G} (hx : x ∈ H ⊔ Subgroup.zpowers k) :
    ∃ h ∈ H, ∃ n : ℤ, x = h * k ^ n := by
  have hle : H ⊔ Subgroup.zpowers k ≤ prodSubgroup hk hk' := by
    refine sup_le ?_ ?_
    · intro h hh
      show ∃ h' ∈ H, ∃ n : ℤ, h = h' * k ^ n
      exact ⟨h, hh, 0, by rw [zpow_zero, mul_one]⟩
    · rw [Subgroup.zpowers_le]
      show ∃ h' ∈ H, ∃ n : ℤ, k = h' * k ^ n
      exact ⟨1, H.one_mem, 1, by rw [zpow_one, one_mul]⟩
  exact hle hx

/-- If `k ^ m ∈ H` with `m > 0`, every element of `H ⊔ ⟨k⟩` is `h * k ^ r` with `r < m`. -/
theorem exists_mul_pow_lt (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {m : ℕ} (hm : 0 < m) (hkm : k ^ m ∈ H) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers k) : ∃ h ∈ H, ∃ r : ℕ, r < m ∧ x = h * k ^ r := by
  obtain ⟨h, hh, n, rfl⟩ := exists_mul_zpow_of_mem_sup hk hk' hx
  have hm' : (0 : ℤ) < m := by omega
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg n hm'.ne')
  have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos n hm'
  rw [hr] at hlt
  have hdecomp : n = (m : ℤ) * (n / (m : ℤ)) + (r : ℤ) := by
    rw [← hr]
    exact (Int.mul_ediv_add_emod n m).symm
  refine ⟨h * (k ^ m) ^ (n / (m : ℤ)), H.mul_mem hh (H.zpow_mem hkm _), r, by omega, ?_⟩
  conv_lhs => rw [hdecomp]
  rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, mul_assoc]

/-! ## Exactly one block in every row and column -/

variable {m : ℕ}

theorem eq_of_inv_pow_mul_pow_mem (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H) {a b : ℕ}
    (ha : a < m) (hb : b < m) (h : (k ^ a)⁻¹ * k ^ b ∈ H) : a = b := by
  rcases Nat.le_total a b with hab | hab
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, inv_mul_cancel_left] at h
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exact absurd h (hmin d hd (by omega))
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at h
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exact absurd (inv_mem_iff.mp h) (hmin d hd (by omega))

/-- At most one used block in each row. -/
theorem cc_row_unique (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H) {x : G} {i j j' : ℕ}
    (hj : j < m) (hj' : j' < m) (h : cc k x i j ∈ H) (h' : cc k x i j' ∈ H) : j = j' := by
  have hm := H.mul_mem (H.inv_mem h) h'
  rw [cc_inv, cc_mul, inv_mul_cancel, cc, mul_one] at hm
  exact eq_of_inv_pow_mul_pow_mem hmin hj hj' hm

/-- At most one used block in each column. -/
theorem cc_col_unique (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H) {x : G} {i i' j : ℕ}
    (hi : i < m) (hi' : i' < m) (h : cc k x i j ∈ H) (h' : cc k x i' j ∈ H) : i = i' := by
  have hm := H.mul_mem h (H.inv_mem h')
  rw [cc_inv, cc_mul, mul_inv_cancel, cc, mul_one] at hm
  exact eq_of_inv_pow_mul_pow_mem hmin hi hi' hm

/-- At least one used block in each row, for `x = h * k ^ r`. -/
theorem cc_row_exists (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hkm : k ^ m ∈ H) {h : G}
    (hh : h ∈ H) {r i : ℕ} (hr : r < m) (hi : i < m) : ∃ l, l < m ∧ cc k (h * k ^ r) i l ∈ H := by
  rcases Nat.lt_or_ge i r with hir | hri
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hir.le
    obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le (show e ≤ m by omega)
    refine ⟨f, by omega, ?_⟩
    have heq : cc k (h * k ^ (i + e)) i f = (k ^ i)⁻¹ * h * k ^ i * k ^ m := by
      rw [hf]
      simp only [cc, pow_add, mul_assoc]
    rw [heq]
    exact H.mul_mem (conj_pow_mem' hk' i h hh) hkm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hri
    refine ⟨d, by omega, ?_⟩
    have heq : cc k (h * k ^ r) (r + d) d = (k ^ (r + d))⁻¹ * h * k ^ (r + d) := by
      simp only [cc, pow_add, mul_assoc]
    rw [heq]
    exact conj_pow_mem' hk' (r + d) h hh

end Normalizing

end GroupApproximation.Full.TWWCyclic
