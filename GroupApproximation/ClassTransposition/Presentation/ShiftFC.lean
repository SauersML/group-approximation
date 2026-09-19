import Mathlib

/-!
# The far-commutation lemma of position shifting (Lemma FC)

Research node: `ct-p-z-is-finitely-presented-by-position-shifting`, §3 (Kourovka 17.61 lane).

We have a group `H` and elements `g υ j`, where `υ` is a *type* and `j : ℕ` is a *position*. Some
types are *finite*: they have a width `w τ ≥ 1` and a shift `δ τ`. `FC g δ τ i υ j` says
that conjugating `g υ j` by `g τ i` raises its position by `δ τ`.

Assume the following:
* (D) conjugation by `s` raises every position `≥ 2` by one;
* a finite type `υ₀` of width 1 and shift 1 (the binary split `s` at position 1);
* the base relations `FC τ i υ (i + w τ + k)` for `i ∈ {1, 2}` and `k < 2`.

Then `FC τ i υ j` holds for all `i ≥ 1` and `j ≥ i + w τ` (`fc_of_base`). This is the
Cannon–Floyd–Parry / Brin induction, done for several types at once.
-/

namespace GroupApproximation.ClassTransposition.Presentation

variable {H U : Type*} [Group H]

/-- Conjugating `g υ j` by `g τ i` raises its position by `δ τ`. -/
def FC (g : U → ℕ → H) (δ : U → ℕ) (τ : U) (i : ℕ) (υ : U) (j : ℕ) : Prop :=
  (g τ i)⁻¹ * g υ j * g τ i = g υ (j + δ τ)

section

variable {g : U → ℕ → H} {δ : U → ℕ} {s : H}

/-- Iterating (D): conjugation by `s ^ k` raises positions `≥ 2` by `k`. -/
theorem shift_pow (hD : ∀ υ j, 2 ≤ j → g υ (j + 1) = s⁻¹ * g υ j * s) (k : ℕ) :
    ∀ υ m, 2 ≤ m → g υ (m + k) = (s ^ k)⁻¹ * g υ m * s ^ k := by
  induction k with
  | zero => intro υ m _; simp
  | succ k ih =>
    intro υ m hm
    rw [show m + (k + 1) = m + k + 1 by omega, hD υ (m + k) (by omega), ih υ m hm, pow_succ]
    group

/-- **Step A.** A far-commutation relation at positions `(2, t)` gives the one at
`(2 + k, t + k)`. -/
theorem fc_shift (hD : ∀ υ j, 2 ≤ j → g υ (j + 1) = s⁻¹ * g υ j * s) {τ υ : U} {t : ℕ}
    (k : ℕ) (h : FC g δ τ 2 υ t) (ht : 2 ≤ t) : FC g δ τ (2 + k) υ (t + k) := by
  unfold FC at h ⊢
  have key := shift_pow hD k
  rw [key τ 2 le_rfl, key υ t ht, show t + k + δ τ = t + δ τ + k by omega,
    key υ (t + δ τ) (by omega), ← h]
  group

/-- Step A at an arbitrary position `a ≥ 2`, from the base relation at `(2, 3)`. -/
theorem fc_at (hD : ∀ υ j, 2 ≤ j → g υ (j + 1) = s⁻¹ * g υ j * s) {τ υ : U}
    (h : FC g δ τ 2 υ 3) {a : ℕ} (ha : 2 ≤ a) : FC g δ τ a υ (a + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 + k := ⟨a - 2, by omega⟩
  have := fc_shift hD k h (by norm_num)
  rwa [show 3 + k = 2 + k + 1 by omega] at this

variable {w : U → ℕ} {Fin' : Set U} {υ₀ : U}

/-- **Step B.** For a finite type at position `i ∈ {1, 2}`, the relations at every distance follow
from those at distances `w τ` and `w τ + 1`. -/
theorem fc_step (hD : ∀ υ j, 2 ≤ j → g υ (j + 1) = s⁻¹ * g υ j * s)
    (hυ₀ : υ₀ ∈ Fin') (hw₀ : w υ₀ = 1) (hδ₀ : δ υ₀ = 1) (hw : ∀ τ ∈ Fin', 1 ≤ w τ)
    (hbase : ∀ τ ∈ Fin', ∀ i, (i = 1 ∨ i = 2) → ∀ υ k, k < 2 → FC g δ τ i υ (i + w τ + k))
    {τ : U} (hτ : τ ∈ Fin') {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ∀ n υ, FC g δ τ i υ (i + w τ + n) := by
  have base0 : ∀ υ, FC g δ υ₀ 2 υ 3 := fun υ => by
    have := hbase υ₀ hυ₀ 2 (Or.inr rfl) υ 0 (by norm_num)
    rwa [hw₀] at this
  have hi1 : 1 ≤ i := by omega
  have hwτ := hw τ hτ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro υ
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exact hbase τ hτ i hi υ n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    obtain ⟨a, ha⟩ : ∃ a, a = i + w τ + m := ⟨_, rfl⟩
    have ha2 : 2 ≤ a := by omega
    -- the four relations used
    have hu : FC g δ υ₀ a υ (a + 1) := fc_at hD (base0 υ) ha2
    have ih1 : FC g δ τ i υ₀ a := by rw [ha]; exact ih m (by omega) υ₀
    have ih2 : FC g δ τ i υ (a + 1) := by
      rw [ha, show i + w τ + m + 1 = i + w τ + (m + 1) by omega]
      exact ih (m + 1) (by omega) υ
    have hu' : FC g δ υ₀ (a + δ τ) υ (a + δ τ + 1) := fc_at hD (base0 υ) (by omega)
    unfold FC at hu ih1 ih2 hu' ⊢
    rw [hδ₀] at hu hu'
    rw [show i + w τ + (m + 2) = a + 1 + 1 by omega, ← hu,
      show a + 1 + 1 + δ τ = a + δ τ + 1 + 1 by omega, ← hu',
      show a + δ τ + 1 = a + 1 + δ τ by omega, ← ih2, ← ih1]
    group

/-- **Lemma FC.** The base relations imply every far-commutation relation. -/
theorem fc_of_base (hD : ∀ υ j, 2 ≤ j → g υ (j + 1) = s⁻¹ * g υ j * s)
    (hυ₀ : υ₀ ∈ Fin') (hw₀ : w υ₀ = 1) (hδ₀ : δ υ₀ = 1) (hw : ∀ τ ∈ Fin', 1 ≤ w τ)
    (hbase : ∀ τ ∈ Fin', ∀ i, (i = 1 ∨ i = 2) → ∀ υ k, k < 2 → FC g δ τ i υ (i + w τ + k))
    {τ : U} (hτ : τ ∈ Fin') {i : ℕ} (hi : 1 ≤ i) {υ : U} {j : ℕ} (hj : i + w τ ≤ j) :
    FC g δ τ i υ j := by
  rcases Nat.lt_or_ge i 3 with hi3 | hi3
  · obtain ⟨n, rfl⟩ : ∃ n, j = i + w τ + n := ⟨j - (i + w τ), by omega⟩
    exact fc_step hD hυ₀ hw₀ hδ₀ hw hbase hτ (by omega) n υ
  · obtain ⟨k, rfl⟩ : ∃ k, i = 2 + k := ⟨i - 2, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, j = 2 + w τ + n + k := ⟨j - (2 + k + w τ), by omega⟩
    have hwτ := hw τ hτ
    exact fc_shift hD k (fc_step hD hυ₀ hw₀ hδ₀ hw hbase hτ (Or.inr rfl) n υ) (by omega)

end

/-- A one-parameter relation family that is invariant under the shift holds at every position
`≥ 2` once it holds at position 2 (the left and end windows of the research node). -/
theorem window_of_base {s : H} {r : ℕ → H} (hr : ∀ i, 2 ≤ i → r (i + 1) = s⁻¹ * r i * s)
    (h2 : r 2 = 1) : ∀ i, 2 ≤ i → r i = 1 := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact h2
  | succ i hi ih => rw [hr i hi, ih]; group

end GroupApproximation.ClassTransposition.Presentation
