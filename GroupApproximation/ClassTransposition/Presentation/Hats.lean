import GroupApproximation.ClassTransposition.Presentation.Group

/-!
# Evaluating moves in `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

The element of a move at level `n` is a generator of the stable family `gH`:
* a split of a non-tail box by `p ∈ P ∪ {2}` is `X_p`;
* a split of the tail by an odd `p ∈ P` is `Y_p`, and by `2` it is `1` (a tree edge);
* a swap of two non-tail boxes is `π`, and a swap involving the tail is `ρ`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The type `X p`. -/
def tX (p : ℕ) (hp : p ∈ P' P) : Ty P := Sum.inl ⟨p, hp⟩

/-- The type `Y p`. -/
def tY (p : ℕ) (hp : p ∈ P) : Ty P := Sum.inr (Sum.inl ⟨p, hp⟩)

/-- The type `π`. -/
def tPi : Ty P := Sum.inr (Sum.inr false)

/-- The type `ρ`. -/
def tRho : Ty P := Sum.inr (Sum.inr true)

/-- The element of a move at level `n`, in `H P`. -/
noncomputable def hatH (P : Set ℕ) (m : Move) (n : ℕ) : H P := PresentedGroup.mk _ (hatF P m n)

theorem toH_nil (n : ℕ) : toH P n [] = 1 := map_one _

theorem toH_cons (n : ℕ) (m : Move) (w : List Move) :
    toH P n (m :: w) = hatH P m n * toH P (m.lev n) w := by
  rw [toH, toFree_cons, map_mul]; rfl

theorem toH_single (n : ℕ) (m : Move) : toH P n [m] = hatH P m n := by
  rw [toH_cons, toH_nil, mul_one]

theorem toH_two (n : ℕ) (m₁ m₂ : Move) :
    toH P n [m₁, m₂] = hatH P m₁ n * hatH P m₂ (m₁.lev n) := by
  rw [toH_cons, toH_single]

theorem lev_split {i n : ℕ} (p : ℕ) (h : i < n) : (Move.split i p).lev n = n + p - 1 := by
  simp only [Move.lev, if_pos h]

theorem lev_swap (k n : ℕ) : (Move.swap k).lev n = n := rfl

theorem hatH_split_front {i n p : ℕ} (h : i + 1 < n) (hp : p ∈ P' P) :
    hatH P (.split i p) n = gH (tX p hp) (i + 1) := by
  simp only [hatH, hatF, if_pos h, dif_pos hp]; rfl

theorem hatH_split_tail {i n p : ℕ} (h : i + 1 = n) (hp : p ∈ P) (hp2 : p ≠ 2) :
    hatH P (.split i p) n = gH (tY p hp) (i + 1) := by
  simp only [hatH, hatF, if_neg (show ¬ i + 1 < n by omega),
    if_pos (show i + 1 = n ∧ p ≠ 2 from ⟨h, hp2⟩), dif_pos hp]
  rfl

theorem hatH_split_tail_two {i n : ℕ} (h : i + 1 = n) : hatH P (.split i 2) n = 1 := by
  have e : hatF P (.split i 2) n = 1 := by
    simp only [hatF, if_neg (show ¬ i + 1 < n by omega),
      if_neg (show ¬ (i + 1 = n ∧ (2 : ℕ) ≠ 2) by simp)]
  rw [hatH, e, map_one]

theorem hatH_swap_front {k n : ℕ} (h : k + 2 < n) : hatH P (.swap k) n = gH tPi (k + 1) := by
  simp only [hatH, hatF, if_pos h]; rfl

theorem hatH_swap_tail {k n : ℕ} (h : k + 2 = n) : hatH P (.swap k) n = gH tRho (k + 1) := by
  simp only [hatH, hatF, if_neg (show ¬ k + 2 < n by omega), if_pos h]; rfl

/-- The tail split by an element of `P ∪ {2}`: a `Y` generator, or `1` for the binary split. -/
noncomputable def tailG (P : Set ℕ) (p : ℕ) (j : ℕ) : H P :=
  open Classical in
  if hp : p ∈ P ∧ p ≠ 2 then gH (tY p hp.1) j else 1

theorem hatH_split_tail' {i n p : ℕ} (h : i + 1 = n) (hp : p ∈ P' P) (hP2 : 2 ∉ P) :
    hatH P (.split i p) n = tailG P p (i + 1) := by
  rcases hp with rfl | hp
  · rw [hatH_split_tail_two h, tailG, dif_neg (by simp)]
  · have hp2 : p ≠ 2 := fun e => hP2 (e ▸ hp)
    rw [hatH_split_tail h hp hp2, tailG, dif_pos ⟨hp, hp2⟩]

end GroupApproximation.ClassTransposition.Presentation
