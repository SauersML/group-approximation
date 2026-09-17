import Mathlib
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse, part 1: integer paths with bounded steps

Pure combinatorics on maps `σ : ℤ → ℤ`, used for the orbit cocycle in the Boyle–Tomiyama step.

## Setting

Let `σ : ℤ → ℤ` be a bijection, let `N ≥ 0` be an integer and `L` a natural number such that

* steps are bounded: `|σ (k+1) - σ k| ≤ N` for all `k`;
* far-out values are far out: `|k| ≥ L` implies `|σ k| > N`.

## Orientation (`orientation`)

The sign of `σ k` for `k ≥ L` cannot change: if `σ k > N` then `σ (k+1) ≥ σ k - N > 0 ≥ -N`, so
`σ (k+1) > N`, and symmetrically for the negative side (`forward_sign`, `backward_sign`).
Hence `σ` has constant sign on `[L, ∞)` and on `(-∞, -L]`.  Both signs cannot agree: if
`σ k > N` for all `|k| ≥ L`, then the `2L+1` distinct values `-N-1-i`, `i ≤ 2L`, all have
preimages in the `2L-1` integers `-L < k < L`, contradicting injectivity of the preimage choice
(`not_forall_preimage_window`, a pigeonhole argument); the case of two negative sides is
symmetric.  So either `σ` or `-σ` is a *positive window*: `σ k > N` for `k ≥ L` and `σ k < -N`
for `k ≤ -L` (`IsPositiveWindow`).

## Window counts

For a positive window define `windowCount σ L t = #{0 ≤ i < 2L | t ≤ σ (i - L)}`.

* `windowCount_step`: for `-N ≤ t ≤ N` the unique preimage of `t` lies in the window, so
  `windowCount σ L t = windowCount σ L (t+1) + 1`.
* `windowCount_threshold`: iterating, `windowCount σ L t = windowCount σ L 0 - t` for
  `|t| ≤ N`.
* `windowCount_shift`: shifting the window by one adds `σ L` (counted, `> N ≥ t`) and removes
  `σ (-L)` (not counted, `< -N ≤ t`), so the shifted count is `windowCount σ L t + 1`.
* `windowCount_cocycle`: if `τ k = σ (k+1) - σ 1` and `|σ 1| ≤ N`, then
  `windowCount τ L 0 = windowCount σ L 0 - σ 1 + 1`.

The last identity is the index cocycle `a (T x) + c 1 x = a x + 1` of the Boyle–Tomiyama
conjugacy.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- Indicator of `t ≤ v`. -/
def above (t v : ℤ) : ℤ := if t ≤ v then 1 else 0

/-- Number of window positions `0 ≤ i < 2L` with `t ≤ σ (i - L)`. -/
def windowCount (σ : ℤ → ℤ) (L : ℕ) (t : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (2 * L), above t (σ ((i : ℤ) - L))

/-- `σ` is above `N` right of the window and below `-N` left of it. -/
def IsPositiveWindow (σ : ℤ → ℤ) (N : ℤ) (L : ℕ) : Prop :=
  (∀ k : ℤ, (L : ℤ) ≤ k → N < σ k) ∧ ∀ k : ℤ, k ≤ -(L : ℤ) → σ k < -N

theorem above_split (t v : ℤ) : above t v = above (t + 1) v + if v = t then 1 else 0 := by
  unfold above
  split_ifs <;> omega

theorem windowCount_step {σ : ℤ → ℤ} (hinj : Function.Injective σ)
    (hsurj : Function.Surjective σ) {N : ℤ} {L : ℕ} (hw : IsPositiveWindow σ N L)
    {t : ℤ} (ht₁ : -N ≤ t) (ht₂ : t ≤ N) :
    windowCount σ L t = windowCount σ L (t + 1) + 1 := by
  obtain ⟨k, hk⟩ := hsurj t
  have hk₁ : -(L : ℤ) < k := by
    by_contra h
    have := hw.2 k (by omega)
    omega
  have hk₂ : k < (L : ℤ) := by
    by_contra h
    have := hw.1 k (by omega)
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k + L by omega)
  have hn₂ : n < 2 * L := by omega
  have hsum : (∑ i ∈ Finset.range (2 * L),
      (if σ ((i : ℤ) - L) = t then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.2 hn₂)]
    · rw [if_pos]
      rw [show (n : ℤ) - L = k by omega, hk]
    · intro b _ hb
      rw [if_neg]
      intro hbt
      have hbk : (b : ℤ) - L = k := hinj (hbt.trans hk.symm)
      exact hb (by omega)
  have hsplit : ∀ i ∈ Finset.range (2 * L), above t (σ ((i : ℤ) - L)) =
      above (t + 1) (σ ((i : ℤ) - L)) + if σ ((i : ℤ) - L) = t then 1 else 0 :=
    fun i _ => above_split _ _
  unfold windowCount
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hsum]

theorem windowCount_threshold {σ : ℤ → ℤ} (hinj : Function.Injective σ)
    (hsurj : Function.Surjective σ) {N : ℤ} {L : ℕ} (hw : IsPositiveWindow σ N L)
    {t : ℤ} (ht₁ : -N ≤ t) (ht₂ : t ≤ N) :
    windowCount σ L t = windowCount σ L 0 - t := by
  have hpos : ∀ n : ℕ, (n : ℤ) ≤ N → windowCount σ L n = windowCount σ L 0 - n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := windowCount_step hinj hsurj hw (t := (n : ℤ)) (by omega) (by omega)
      have h2 := ih (by omega)
      rw [Nat.cast_add_one]
      omega
  have hneg : ∀ n : ℕ, (n : ℤ) ≤ N → windowCount σ L (-(n : ℤ)) = windowCount σ L 0 + n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := windowCount_step hinj hsurj hw (t := -((n : ℤ) + 1)) (by omega) (by omega)
      have h2 := ih (by omega)
      rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by omega] at h1
      rw [Nat.cast_add_one]
      omega
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · exact hpos n ht₂
  · have h := hneg n (by omega)
    omega

theorem windowCount_shift {σ : ℤ → ℤ} {N : ℤ} {L : ℕ} (hw : IsPositiveWindow σ N L) {t : ℤ}
    (ht₁ : -N ≤ t) (ht₂ : t ≤ N) :
    ∑ i ∈ Finset.range (2 * L), above t (σ ((i : ℤ) - L + 1)) = windowCount σ L t + 1 := by
  have h₁ := Finset.sum_range_succ' (fun j : ℕ => above t (σ ((j : ℤ) - L))) (2 * L)
  have h₂ := Finset.sum_range_succ (fun j : ℕ => above t (σ ((j : ℤ) - L))) (2 * L)
  beta_reduce at h₁ h₂
  have h₀ : above t (σ (((0 : ℕ) : ℤ) - L)) = 0 := by
    unfold above
    rw [if_neg]
    have := hw.2 (((0 : ℕ) : ℤ) - L) (by omega)
    omega
  have h₃ : above t (σ (((2 * L : ℕ) : ℤ) - L)) = 1 := by
    unfold above
    rw [if_pos]
    have := hw.1 (((2 * L : ℕ) : ℤ) - L) (by omega)
    omega
  have hcongr : ∑ i ∈ Finset.range (2 * L), above t (σ (((i + 1 : ℕ) : ℤ) - L)) =
      ∑ i ∈ Finset.range (2 * L), above t (σ ((i : ℤ) - L + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((i + 1 : ℕ) : ℤ) - L = (i : ℤ) - L + 1 by omega]
  unfold windowCount
  omega

theorem windowCount_cocycle {σ τ : ℤ → ℤ} (hinj : Function.Injective σ)
    (hsurj : Function.Surjective σ) {N : ℤ} {L : ℕ} (hw : IsPositiveWindow σ N L)
    (h1 : -N ≤ σ 1 ∧ σ 1 ≤ N) (hτ : ∀ k, τ k = σ (k + 1) - σ 1) :
    windowCount τ L 0 = windowCount σ L 0 - σ 1 + 1 := by
  have hc : windowCount τ L 0 =
      ∑ i ∈ Finset.range (2 * L), above (σ 1) (σ ((i : ℤ) - L + 1)) := by
    unfold windowCount
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold above
    rw [hτ]
    split_ifs <;> omega
  rw [hc, windowCount_shift hw h1.1 h1.2, windowCount_threshold hinj hsurj hw h1.1 h1.2]

section Orientation

variable {σ : ℤ → ℤ} {N : ℤ} {L : ℕ}

theorem forward_sign (hN : 0 ≤ N) (hstep : ∀ k, σ (k + 1) - σ k ≤ N ∧ σ k - σ (k + 1) ≤ N)
    (hout : ∀ k, ((L : ℤ) ≤ k ∨ k ≤ -(L : ℤ)) → N < σ k ∨ σ k < -N) (n : ℕ) :
    (N < σ L → N < σ ((L : ℤ) + n)) ∧ (σ L < -N → σ ((L : ℤ) + n) < -N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hout ((L : ℤ) + (n + 1 : ℕ)) (Or.inl (by omega))
    have hs := hstep ((L : ℤ) + n)
    rw [show (L : ℤ) + ((n + 1 : ℕ) : ℤ) = (L : ℤ) + n + 1 by omega] at h ⊢
    constructor
    · intro hL
      have := ih.1 hL
      omega
    · intro hL
      have := ih.2 hL
      omega

theorem backward_sign (hN : 0 ≤ N) (hstep : ∀ k, σ (k + 1) - σ k ≤ N ∧ σ k - σ (k + 1) ≤ N)
    (hout : ∀ k, ((L : ℤ) ≤ k ∨ k ≤ -(L : ℤ)) → N < σ k ∨ σ k < -N) (n : ℕ) :
    (N < σ (-(L : ℤ)) → N < σ (-(L : ℤ) - n)) ∧
      (σ (-(L : ℤ)) < -N → σ (-(L : ℤ) - n) < -N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hout (-(L : ℤ) - (n + 1 : ℕ)) (Or.inr (by omega))
    have hs := hstep (-(L : ℤ) - (n + 1 : ℕ))
    rw [show -(L : ℤ) - ((n + 1 : ℕ) : ℤ) + 1 = -(L : ℤ) - n by omega] at hs
    constructor
    · intro hL
      have := ih.1 hL
      omega
    · intro hL
      have := ih.2 hL
      omega

/-- Pigeonhole: infinitely many distinct values cannot all have preimages in `(-L, L)`. -/
theorem not_forall_preimage_window (L : ℕ) (σ : ℤ → ℤ) (v : ℕ → ℤ)
    (hv : Function.Injective v) (hpre : ∀ i, ∃ k, -(L : ℤ) < k ∧ k < L ∧ σ k = v i) : False := by
  choose g hg₁ hg₂ hg₃ using hpre
  have hmaps : Set.MapsTo g (Finset.range (2 * L + 1) : Set ℕ)
      (((Finset.range (2 * L)).image fun j : ℕ => (j : ℤ) - L : Finset ℤ) : Set ℤ) := by
    intro i _
    have hi₁ := hg₁ i
    have hi₂ := hg₂ i
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ g i + L by omega)
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨n, by omega, by omega⟩
  have hcard : ((Finset.range (2 * L)).image fun j : ℕ => (j : ℤ) - L).card <
      (Finset.range (2 * L + 1)).card := by
    calc _ ≤ (Finset.range (2 * L)).card := Finset.card_image_le
      _ < _ := by rw [Finset.card_range, Finset.card_range]; omega
  obtain ⟨i, _, j, _, hij, hgij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact hij (hv ((hg₃ i).symm.trans ((congrArg σ hgij).trans (hg₃ j))))

theorem orientation (hsurj : Function.Surjective σ) (hN : 0 ≤ N)
    (hstep : ∀ k, σ (k + 1) - σ k ≤ N ∧ σ k - σ (k + 1) ≤ N)
    (hout : ∀ k, ((L : ℤ) ≤ k ∨ k ≤ -(L : ℤ)) → N < σ k ∨ σ k < -N) :
    IsPositiveWindow σ N L ∨ IsPositiveWindow (fun k => -σ k) N L := by
  have hfwd : ∀ k : ℤ, (L : ℤ) ≤ k →
      (N < σ L → N < σ k) ∧ (σ L < -N → σ k < -N) := by
    intro k hk
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k - L by omega)
    rw [show k = (L : ℤ) + n by omega]
    exact forward_sign hN hstep hout n
  have hbwd : ∀ k : ℤ, k ≤ -(L : ℤ) →
      (N < σ (-(L : ℤ)) → N < σ k) ∧ (σ (-(L : ℤ)) < -N → σ k < -N) := by
    intro k hk
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -(L : ℤ) - k by omega)
    rw [show k = -(L : ℤ) - n by omega]
    exact backward_sign hN hstep hout n
  have hL := hout (L : ℤ) (Or.inl le_rfl)
  have hL' := hout (-(L : ℤ)) (Or.inr le_rfl)
  rcases hL with hL | hL <;> rcases hL' with hL' | hL'
  · exfalso
    refine not_forall_preimage_window L σ (fun i => -N - 1 - i) (fun i j hij => ?_) fun i => ?_
    · have h : -N - 1 - (i : ℤ) = -N - 1 - j := hij
      omega
    · obtain ⟨k, hk⟩ := hsurj (-N - 1 - i)
      refine ⟨k, ?_, ?_, hk⟩
      · by_contra hc
        have := (hbwd k (by omega)).1 hL'
        omega
      · by_contra hc
        have := (hfwd k (by omega)).1 hL
        omega
  · exact Or.inl ⟨fun k hk => (hfwd k hk).1 hL, fun k hk => (hbwd k hk).2 hL'⟩
  · refine Or.inr ⟨fun k hk => ?_, fun k hk => ?_⟩
    · show N < -σ k
      have := (hfwd k hk).2 hL
      omega
    · show -σ k < -N
      have := (hbwd k hk).1 hL'
      omega
  · exfalso
    refine not_forall_preimage_window L σ (fun i => N + 1 + i) (fun i j hij => ?_) fun i => ?_
    · have h : N + 1 + (i : ℤ) = N + 1 + j := hij
      omega
    · obtain ⟨k, hk⟩ := hsurj (N + 1 + i)
      refine ⟨k, ?_, ?_, hk⟩
      · by_contra hc
        have := (hbwd k (by omega)).2 hL'
        omega
      · by_contra hc
        have := (hfwd k (by omega)).2 hL
        omega

end Orientation

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.above
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.windowCount
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.IsPositiveWindow
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.above_split
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.windowCount_step
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.windowCount_threshold
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.windowCount_shift
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.windowCount_cocycle
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.forward_sign
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.backward_sign
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.not_forall_preimage_window
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.orientation
