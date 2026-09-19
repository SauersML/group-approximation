import GroupApproximation.ClassTransposition.Out.Cont

/-!
# Kourovka 17.57, step 5: an affine class, by counting

Let `Φ : ℕ → ℕ` be a bijection that is eventually a quasi-polynomial: some iterated difference
`(Δ_N)^m Φ` vanishes eventually, where `Δ_N u(n) = u(n + N) - u(n)`. Then along some class
`i + Nℕ` the first difference is eventually constant, i.e. `Φ` is eventually affine there.

No polynomials are used. An integer sequence whose iterated difference vanishes eventually is
eventually constant, or tends to `+∞`, or tends to `-∞` (`trichotomy`). Apply this to the first
difference on each class:
- `-∞` would make `Φ` negative;
- if every class had first difference `→ +∞`, then `Φ` would be superlinear on every class, and
  the `Y + 1` preimages of `{0, …, Y}` would not fit below `Y`.

`affine_of_eventually_affine` then uses profinite continuity to extend an eventually affine
class to the whole class `i + Nℤ`, negative `t` included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

/-- Forward difference with step `N`. -/
def fdiff (N : ℕ) (u : ℕ → ℤ) : ℕ → ℤ := fun n => u (n + N) - u n

def EventuallyConst (a : ℕ → ℤ) : Prop := ∃ n₀ : ℕ, ∃ c : ℤ, ∀ n ≥ n₀, a n = c
def TendsTop (a : ℕ → ℤ) : Prop := ∀ B : ℤ, ∃ n₀ : ℕ, ∀ n ≥ n₀, B ≤ a n
def TendsBot (a : ℕ → ℤ) : Prop := ∀ B : ℤ, ∃ n₀ : ℕ, ∀ n ≥ n₀, a n ≤ B

theorem lower_of_fdiff {a : ℕ → ℤ} {n₀ : ℕ} {c : ℤ} (h : ∀ n ≥ n₀, c ≤ fdiff 1 a n) :
    ∀ k : ℕ, a n₀ + c * k ≤ a (n₀ + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have := h (n₀ + k) (by omega)
    simp only [fdiff] at this
    show a n₀ + c * ((k + 1 : ℕ) : ℤ) ≤ a (n₀ + k + 1)
    push_cast
    rw [mul_add, mul_one]
    linarith

theorem upper_of_fdiff {a : ℕ → ℤ} {n₀ : ℕ} {c : ℤ} (h : ∀ n ≥ n₀, fdiff 1 a n ≤ c) :
    ∀ k : ℕ, a (n₀ + k) ≤ a n₀ + c * k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have := h (n₀ + k) (by omega)
    simp only [fdiff] at this
    show a (n₀ + k + 1) ≤ a n₀ + c * ((k + 1 : ℕ) : ℤ)
    push_cast
    rw [mul_add, mul_one]
    linarith

theorem tendsTop_of_fdiff {a : ℕ → ℤ} {n₀ : ℕ} (h : ∀ n ≥ n₀, 1 ≤ fdiff 1 a n) :
    TendsTop a := by
  intro B
  refine ⟨n₀ + (B - a n₀).toNat, fun n hn => ?_⟩
  have hl := lower_of_fdiff h (n - n₀)
  rw [show n₀ + (n - n₀) = n by omega] at hl
  have h0 : (B - a n₀).toNat ≤ n - n₀ := by omega
  have h1 : ((B - a n₀).toNat : ℤ) ≤ ((n - n₀ : ℕ) : ℤ) := by exact_mod_cast h0
  have h2 : ((B - a n₀).toNat : ℤ) ≥ B - a n₀ := Int.self_le_toNat _
  linarith

theorem tendsBot_of_fdiff {a : ℕ → ℤ} {n₀ : ℕ} (h : ∀ n ≥ n₀, fdiff 1 a n ≤ -1) :
    TendsBot a := by
  intro B
  refine ⟨n₀ + (a n₀ - B).toNat, fun n hn => ?_⟩
  have hl := upper_of_fdiff h (n - n₀)
  rw [show n₀ + (n - n₀) = n by omega] at hl
  have h0 : (a n₀ - B).toNat ≤ n - n₀ := by omega
  have h1 : ((a n₀ - B).toNat : ℤ) ≤ ((n - n₀ : ℕ) : ℤ) := by exact_mod_cast h0
  have h2 : ((a n₀ - B).toNat : ℤ) ≥ a n₀ - B := Int.self_le_toNat _
  linarith

/-- An integer sequence whose `k`-th difference vanishes eventually is eventually constant, or
tends to `+∞`, or tends to `-∞`. -/
theorem trichotomy : ∀ (k : ℕ) (a : ℕ → ℤ), (∃ n₀ : ℕ, ∀ n ≥ n₀, (fdiff 1)^[k] a n = 0) →
    EventuallyConst a ∨ TendsTop a ∨ TendsBot a
  | 0, a, ⟨n₀, h⟩ => Or.inl ⟨n₀, 0, h⟩
  | k + 1, a, ⟨n₀, h⟩ => by
    have hb : ∃ n₀ : ℕ, ∀ n ≥ n₀, (fdiff 1)^[k] (fdiff 1 a) n = 0 :=
      ⟨n₀, fun n hn => by rw [← Function.iterate_succ_apply]; exact h n hn⟩
    rcases trichotomy k (fdiff 1 a) hb with ⟨n₁, c, hc⟩ | htop | hbot
    · rcases lt_trichotomy c 0 with hneg | hzero | hpos
      · exact Or.inr (Or.inr (tendsBot_of_fdiff (n₀ := n₁) fun n hn => by rw [hc n hn]; omega))
      · refine Or.inl ⟨n₁, a n₁, fun n hn => ?_⟩
        have hl := lower_of_fdiff (a := a) (n₀ := n₁) (c := 0) (fun m hm => by rw [hc m hm, hzero])
          (n - n₁)
        have hu := upper_of_fdiff (a := a) (n₀ := n₁) (c := 0) (fun m hm => by rw [hc m hm, hzero])
          (n - n₁)
        rw [show n₁ + (n - n₁) = n by omega] at hl hu
        linarith
      · exact Or.inr (Or.inl (tendsTop_of_fdiff (n₀ := n₁) fun n hn => by rw [hc n hn]; omega))
    · obtain ⟨n₁, hn₁⟩ := htop 1
      exact Or.inr (Or.inl (tendsTop_of_fdiff hn₁))
    · obtain ⟨n₁, hn₁⟩ := hbot (-1)
      exact Or.inr (Or.inr (tendsBot_of_fdiff hn₁))

/-- Differences commute with restriction to a residue class. -/
theorem iterate_fdiff_class (N i : ℕ) : ∀ (m : ℕ) (u : ℕ → ℤ) (t : ℕ),
    (fdiff 1)^[m] (fun t => u (i + N * t)) t = ((fdiff N)^[m] u) (i + N * t)
  | 0, u, t => rfl
  | m + 1, u, t => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have e : fdiff 1 (fun t => u (i + N * t)) = fun t => fdiff N u (i + N * t) := by
      funext t
      simp only [fdiff]
      rw [show i + N * (t + 1) = i + N * t + N by ring]
    rw [e]
    exact iterate_fdiff_class N i m (fdiff N u) t


theorem iterate_fdiff_class_eq_zero {Φ : ℕ → ℤ} {N m n₀ : ℕ} (hN : 0 < N)
    (hq : ∀ n ≥ n₀, (fdiff N)^[m] Φ n = 0) (i : ℕ) :
    ∀ t ≥ n₀, (fdiff 1)^[m] (fdiff 1 (fun t => Φ (i + N * t))) t = 0 := by
  intro t ht
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  simp only [fdiff]
  rw [iterate_fdiff_class N i m Φ (t + 1), iterate_fdiff_class N i m Φ t,
    hq (i + N * (t + 1)) (by nlinarith), hq (i + N * t) (by nlinarith), sub_self]

/-- **Step 5 (counting).** A bijection `Φ : ℕ → ℕ` that is eventually quasi-polynomial has a
residue class on which its first difference is eventually constant. -/
theorem exists_eventually_affine_class {Φ : ℕ → ℕ} (hΦ : Function.Bijective Φ) {N m n₀ : ℕ}
    (hN : 0 < N) (hq : ∀ n ≥ n₀, (fdiff N)^[m] (fun n => (Φ n : ℤ)) n = 0) :
    ∃ i < N, EventuallyConst (fdiff 1 (fun t => (Φ (i + N * t) : ℤ))) := by
  by_contra hcon
  push Not at hcon
  have hbig : ∀ i, i < N → ∃ t₀ : ℕ, ∀ t ≥ t₀,
      2 * (N : ℤ) ≤ fdiff 1 (fun t => (Φ (i + N * t) : ℤ)) t := by
    intro i hi
    rcases trichotomy m (fdiff 1 (fun t => (Φ (i + N * t) : ℤ)))
        ⟨n₀, iterate_fdiff_class_eq_zero hN hq i⟩ with hc | ht | hb
    · exact absurd hc (hcon i hi)
    · exact ht (2 * N)
    · exfalso
      obtain ⟨t₁, ht₁⟩ := hb (-1)
      obtain ⟨t₂, ht₂⟩ := tendsBot_of_fdiff ht₁ (-1)
      have h1 : (Φ (i + N * t₂) : ℤ) ≤ -1 := ht₂ t₂ le_rfl
      have h2 : (0 : ℤ) ≤ (Φ (i + N * t₂) : ℤ) := by positivity
      linarith
  choose! T hT using hbig
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = ∑ i ∈ Finset.range N, T i := ⟨_, rfl⟩
  have hTS : ∀ i, i < N → T i ≤ S := by
    intro i hi
    rw [hS]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (T j)) (Finset.mem_range.mpr hi)
  have hlow : ∀ i, i < N → ∀ t : ℕ, S ≤ t →
      2 * (N : ℤ) * ((t - S : ℕ) : ℤ) ≤ (Φ (i + N * t) : ℤ) := by
    intro i hi t ht
    have hl := lower_of_fdiff (a := fun t => (Φ (i + N * t) : ℤ)) (n₀ := S) (c := 2 * N)
      (fun n hn => hT i hi n (le_trans (hTS i hi) hn)) (t - S)
    rw [show S + (t - S) = t by omega] at hl
    have hl' : (Φ (i + N * S) : ℤ) + 2 * N * ((t - S : ℕ) : ℤ) ≤ (Φ (i + N * t) : ℤ) := hl
    have h0 : (0 : ℤ) ≤ (Φ (i + N * S) : ℤ) := by positivity
    linarith
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ y, Φ (g y) = y :=
    ⟨Function.surjInv hΦ.2, Function.surjInv_eq hΦ.2⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = 2 * N * (S + 1) + 2 := ⟨_, rfl⟩
  have hmaps : ∀ y, y ≤ Y → g y < Y := by
    intro y hy
    have hdecomp : g y % N + N * (g y / N) = g y := Nat.mod_add_div (g y) N
    have hi : g y % N < N := Nat.mod_lt (g y) hN
    by_cases ht : g y / N < S
    · have h1 : N * (g y / N + 1) ≤ N * S := Nat.mul_le_mul_left N (Nat.succ_le_of_lt ht)
      have h2 : N * S ≤ Y := by
        rw [hY]
        nlinarith [Nat.zero_le (N * S)]
      have h3 : g y < N * (g y / N + 1) := by nlinarith
      exact lt_of_lt_of_le h3 (le_trans h1 h2)
    · push Not at ht
      have hb := hlow (g y % N) hi (g y / N) ht
      rw [hdecomp, hg] at hb
      have hq' : ((g y / N - S : ℕ) : ℤ) = ((g y / N : ℕ) : ℤ) - S := Nat.cast_sub ht
      rw [hq'] at hb
      have hy' : (y : ℤ) ≤ 2 * N * (S + 1) + 2 := by
        rw [hY] at hy
        exact_mod_cast hy
      have hi' : ((g y % N : ℕ) : ℤ) + 1 ≤ N := by exact_mod_cast hi
      have hd' : ((g y % N : ℕ) : ℤ) + N * ((g y / N : ℕ) : ℤ) = (g y : ℤ) := by
        exact_mod_cast hdecomp
      have hlt : (g y : ℤ) < 2 * N * (S + 1) + 2 := by linarith
      have hY' : ((Y : ℕ) : ℤ) = 2 * N * (S + 1) + 2 := by
        rw [hY]
        push_cast
        ring
      have : (g y : ℤ) < (Y : ℤ) := by rw [hY']; exact hlt
      exact_mod_cast this
  have hcard := Finset.card_le_card_of_injOn g (s := Finset.range (Y + 1))
    (t := Finset.range Y)
    (fun y hy => Finset.mem_range.mpr (hmaps y (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))))
    (fun y₁ _ y₂ _ h => by rw [← hg y₁, ← hg y₂, h])
  simp only [Finset.card_range] at hcard
  omega

/-- **Step 5 (extension).** A profinitely continuous `h` that is affine on the tail of a
residue class is affine on the whole class. -/
theorem affine_of_eventually_affine {h : ℤ → ℤ} (hc : IsProfinitelyContinuous h)
    {i N A c t₀ : ℤ} (hev : ∀ t ≥ t₀, h (i + t * N) = A + c * t) (t : ℤ) :
    h (i + t * N) = A + c * t := by
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = h (i + t * N) - (A + c * t) := ⟨_, rfl⟩
  obtain ⟨P, hP, hPM⟩ := hc (|D| + 1) (by positivity)
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (|D| + 1) * (|t₀ - t| + 1) := ⟨_, rfl⟩
  have hK1 : |t₀ - t| + 1 ≤ K := by
    rw [hK]
    nlinarith [abs_nonneg D, abs_nonneg (t₀ - t)]
  have ht' : t₀ ≤ t + P * K := by
    have h1 := le_abs_self (t₀ - t)
    have h2 : K ≤ P * K := by nlinarith [abs_nonneg (t₀ - t)]
    linarith
  have h1 := hPM (i + (t + P * K) * N) (i + t * N) ⟨K * N, by ring⟩
  rw [hev _ ht'] at h1
  have h2 : (|D| + 1) ∣ c * P * K := ⟨c * P * (|t₀ - t| + 1), by rw [hK]; ring⟩
  have h3 : (|D| + 1) ∣ D := by
    have e : D = c * P * K - (A + c * (t + P * K) - h (i + t * N)) := by
      rw [hD]
      ring
    rw [e]
    exact dvd_sub h2 h1
  have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by linarith)
  linarith

end GroupApproximation.ClassTransposition.Out
