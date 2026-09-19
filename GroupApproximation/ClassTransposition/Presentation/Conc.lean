import GroupApproximation.ClassTransposition.Presentation.ListBlock
import GroupApproximation.ClassTransposition.Presentation.Group

/-!
# The concrete elements of moves

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

A move `m` at level `n` has the concrete element `conc m n = frac (comb n') (m.app (comb n))`,
which maps the comb with `n'` boxes onto the move applied to the comb with `n` boxes. It does not
depend on the level while the move stays away from the tail (`conc_stable`). Conjugation by the
concrete shift `σ = conc (split 0 2) _` moves it one box right (`conc_up`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- The concrete element of a move at level `n`. -/
noncomputable def conc (m : Move) (n : ℕ) : Perm ℤ := frac (comb (m.lev n)) (m.app (comb n))

theorem splitAt_of_le : ∀ (b : List Box) (i p : ℕ), b.length ≤ i → splitAt b i p = b
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => by simp at h
  | E :: b, i + 1, p, h => by
    simp only [splitAt]
    rw [splitAt_of_le b i p (by simp at h; omega)]

theorem length_app (b : List Box) (m : Move) : (m.app b).length = m.lev b.length := by
  cases m with
  | split i p =>
    show (splitAt b i p).length = _
    by_cases h : i < b.length
    · rw [length_splitAt b i p h, lev_split p h]
    · rw [splitAt_of_le b i p (by omega)]
      simp only [Move.lev, if_neg h]
  | swap k => exact length_swapAt b k

theorem length_real : ∀ (b : List Box) (w : List Move), (real b w).length = levW b.length w
  | _, [] => rfl
  | b, m :: w => by rw [real_cons, levW_cons, length_real (m.app b) w, length_app]

theorem isPart_comb_app {n : ℕ} (hn : 0 < n) {m : Move} (hm : m.Ok) : IsPart (m.app (comb n)) :=
  isPart_app (isPart_comb n hn) hm

theorem lev_pos {m : Move} {n : ℕ} (hn : 0 < n) (hm : m.Ok) : 0 < m.lev n := by
  cases m with
  | split i p =>
    simp only [Move.Ok] at hm
    simp only [Move.lev]
    split_ifs <;> omega
  | swap k => exact hn

/-- Refining both partitions by the same split does not change `frac`. -/
theorem frac_splitAt {b c : List Box} (hb : IsPart b) (hc : IsPart c) (hl : b.length = c.length)
    (i : ℕ) {p : ℕ} (hp : 0 < p) : frac (splitAt b i p) (splitAt c i p) = frac b c :=
  (eq_frac (isPart_splitAt hb i hp) (isPart_splitAt hc i hp)
    (forall₂_splitAt (frac_canon hb hc hl) i p)).symm

/-- The comb with `n + 1` boxes is the tail split of the comb with `n` boxes. -/
theorem comb_succ_tail {n : ℕ} (hn : 0 < n) : comb (n + 1) = splitAt (comb n) (n - 1) 2 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show comb (n + 2) = splitAt (comb (n + 1)) (n + 1 - 1) 2
  rw [Nat.add_sub_cancel, splitAt_comb_tail]

/-- A move before the tail commutes with the tail split. -/
theorem app_tail {b : List Box} {m : Move} (hm : m.Front b.length) (hm0 : m.Ok) :
    m.app (splitAt b (b.length - 1) 2) = splitAt (m.app b) (m.lev b.length - 1) 2 := by
  cases m with
  | split i p =>
    simp only [Move.Front] at hm
    simp only [Move.Ok] at hm0
    show splitAt (splitAt b (b.length - 1) 2) i p = splitAt (splitAt b i p) _ 2
    rw [lev_split p (by omega), ← splitAt_splitAt_far p b i (b.length - 1) 2 (by omega)]
    congr 1
    omega
  | swap k =>
    simp only [Move.Front] at hm
    show swapAt (splitAt b (b.length - 1) 2) k = splitAt (swapAt b k) (b.length - 1) 2
    rw [splitAt_swapAt_right 2 b k (b.length - 1) (by omega)]

/-- **Stabilization.** A move before the tail has the same concrete element one level up. -/
theorem conc_stable {m : Move} {n : ℕ} (hn : 0 < n) (hm : m.Front n) (hm0 : m.Ok) :
    conc m (n + 1) = conc m n := by
  have hL := lev_pos hn hm0
  have hlen : (m.app (comb n)).length = m.lev n := by rw [length_app, length_comb]
  unfold conc
  rw [lev_stable m n hm, comb_succ_tail hL, comb_succ_tail hn,
    show m.app (splitAt (comb n) (n - 1) 2) = splitAt (m.app (comb n)) (m.lev n - 1) 2 by
      have := app_tail (b := comb n) (by rw [length_comb]; exact hm) hm0
      rwa [length_comb] at this]
  exact frac_splitAt (isPart_comb _ hL) (isPart_comb_app hn hm0) (by rw [length_comb, hlen])
    (m.lev n - 1) (by norm_num)

end GroupApproximation.ClassTransposition.Presentation
