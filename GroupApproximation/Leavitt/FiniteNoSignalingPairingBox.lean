import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# An exact finite no-signaling pairing box

This file records the smallest counterexample to the claim that perfect
labelwise pairing correlations with common marginals must come from whole
response maps.  The label space is `F₂²`, represented by two booleans.  For
each requested pairing value, sample uniformly among nonzero output pairs
having that value.  Both endpoint marginals are uniform on the three nonzero
labels, independently of the requested value.

The construction is deliberately finite and explicit.  It is a no-go lemma
for a proposed extraction shortcut, not an ingredient in the positive
paired-quotient floor.
-/

namespace GroupApproximation
namespace FiniteNoSignalingPairingBox

noncomputable section

/-- The four labels of the rank-two binary pairing. -/
abbrev Label := Bool × Bool

/-- The zero label. -/
def zeroLabel : Label := (false, false)

/-- The standard dot product on `F₂²`. -/
def pairing (x y : Label) : Bool :=
  Bool.xor (x.1 && y.1) (x.2 && y.2)

/-- Uniform weight on the nonzero output pairs with prescribed pairing
value.  There are three such pairs for value zero and six for value one. -/
def pairingBoxWeight (c : Bool) (x y : Label) : ℝ :=
  if x = zeroLabel then 0
  else if y = zeroLabel then 0
  else if pairing x y = c then
    if c = false then (1 : ℝ) / 3 else (1 : ℝ) / 6
  else 0

theorem pairingBoxWeight_nonnegative (c : Bool) (x y : Label) :
    0 ≤ pairingBoxWeight c x y := by
  unfold pairingBoxWeight
  split_ifs <;> norm_num

/-- Every row marginal is zero at the zero label and `1/3` at each nonzero
label, independently of the requested pairing value. -/
theorem pairingBoxWeight_row (c : Bool) (x : Label) :
    ∑ y, pairingBoxWeight c x y =
      if x = zeroLabel then 0 else (1 : ℝ) / 3 := by
  rcases x with ⟨x₀, x₁⟩
  fin_cases x₀ <;> fin_cases x₁ <;> fin_cases c <;>
    norm_num [pairingBoxWeight, pairing, zeroLabel, Fintype.sum_prod_type]

/-- Every column marginal has the same common form. -/
theorem pairingBoxWeight_column (c : Bool) (y : Label) :
    ∑ x, pairingBoxWeight c x y =
      if y = zeroLabel then 0 else (1 : ℝ) / 3 := by
  rcases y with ⟨y₀, y₁⟩
  fin_cases y₀ <;> fin_cases y₁ <;> fin_cases c <;>
    norm_num [pairingBoxWeight, pairing, zeroLabel, Fintype.sum_prod_type]

/-- Each prescribed-value box is a probability law. -/
theorem pairingBoxWeight_total (c : Bool) :
    ∑ x, ∑ y, pairingBoxWeight c x y = 1 := by
  simp_rw [pairingBoxWeight_row]
  norm_num [zeroLabel, Fintype.sum_prod_type]

/-- Positive support lies on nonzero labels of the prescribed pairing
value. -/
theorem pairingBoxWeight_support (c : Bool) (x y : Label)
    (h : pairingBoxWeight c x y ≠ 0) :
    x ≠ zeroLabel ∧ y ≠ zeroLabel ∧ pairing x y = c := by
  by_cases hx : x = zeroLabel
  · simp [pairingBoxWeight, hx] at h
  by_cases hy : y = zeroLabel
  · simp [pairingBoxWeight, hx, hy] at h
  by_cases hp : pairing x y = c
  · exact ⟨hx, hy, hp⟩
  · simp [pairingBoxWeight, hx, hy, hp] at h

/-- The diagonal context requests the source pairing value. -/
def diagonalBox (v w x y : Label) : ℝ :=
  pairingBoxWeight (pairing v w) x y

/-- The crossed context requests pairing value zero. -/
def crossedBox (_v _w x y : Label) : ℝ :=
  pairingBoxWeight false x y

theorem diagonalBox_support (v w x y : Label)
    (h : diagonalBox v w x y ≠ 0) :
    x ≠ zeroLabel ∧ y ≠ zeroLabel ∧ pairing x y = pairing v w := by
  exact pairingBoxWeight_support (pairing v w) x y h

theorem crossedBox_support (v w x y : Label)
    (h : crossedBox v w x y ≠ 0) :
    x ≠ zeroLabel ∧ y ≠ zeroLabel ∧ pairing x y = false := by
  exact pairingBoxWeight_support false x y h

/-- The diagonal and crossed contexts have exactly the same left marginal. -/
theorem diagonal_crossed_left_marginal (v w v' w' x : Label) :
    (∑ y, diagonalBox v w x y) = ∑ y, crossedBox v' w' x y := by
  change (∑ y, pairingBoxWeight (pairing v w) x y) =
    ∑ y, pairingBoxWeight false x y
  rw [pairingBoxWeight_row, pairingBoxWeight_row]

/-- The diagonal and crossed contexts have exactly the same right marginal. -/
theorem diagonal_crossed_right_marginal (v w v' w' y : Label) :
    (∑ x, diagonalBox v w x y) = ∑ x, crossedBox v' w' x y := by
  change (∑ x, pairingBoxWeight (pairing v w) x y) =
    ∑ x, pairingBoxWeight false x y
  rw [pairingBoxWeight_column, pairingBoxWeight_column]

/-- The exact rank-two no-signaling countermodel: both diagonal boxes and
the crossed-zero box are normalized nonnegative laws, their endpoint
marginals agree, and every positive output satisfies the requested pairing
constraint. -/
theorem exists_exact_three_context_pairing_box :
    ∃ (q₀₀ q₀₁ q₁₁ : Label → Label → Label → Label → ℝ),
      (∀ v w x y, 0 ≤ q₀₀ v w x y) ∧
      (∀ v w, ∑ x, ∑ y, q₀₀ v w x y = 1) ∧
      (∀ v w x y, q₀₀ v w x y ≠ 0 → pairing x y = pairing v w) ∧
      (∀ v w x y, 0 ≤ q₀₁ v w x y) ∧
      (∀ v w, ∑ x, ∑ y, q₀₁ v w x y = 1) ∧
      (∀ v w x y, q₀₁ v w x y ≠ 0 → pairing x y = false) ∧
      (∀ v w x y, 0 ≤ q₁₁ v w x y) ∧
      (∀ v w, ∑ x, ∑ y, q₁₁ v w x y = 1) ∧
      (∀ v w x y, q₁₁ v w x y ≠ 0 → pairing x y = pairing v w) ∧
      (∀ v w v' w' x, (∑ y, q₀₀ v w x y) = ∑ y, q₀₁ v' w' x y) ∧
      (∀ v w v' w' y, (∑ x, q₀₁ v w x y) = ∑ x, q₁₁ v' w' x y) := by
  refine ⟨diagonalBox, crossedBox, diagonalBox,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w x y
    exact pairingBoxWeight_nonnegative (pairing v w) x y
  · intro v w
    exact pairingBoxWeight_total (pairing v w)
  · intro v w x y h
    exact (diagonalBox_support v w x y h).2.2
  · intro v w x y
    exact pairingBoxWeight_nonnegative false x y
  · intro v w
    exact pairingBoxWeight_total false
  · intro v w x y h
    exact (crossedBox_support v w x y h).2.2
  · intro v w x y
    exact pairingBoxWeight_nonnegative (pairing v w) x y
  · intro v w
    exact pairingBoxWeight_total (pairing v w)
  · intro v w x y h
    exact (diagonalBox_support v w x y h).2.2
  · exact diagonal_crossed_left_marginal
  · intro v w v' w' y
    exact (diagonal_crossed_right_marginal v' w' v w y).symm

end
end FiniteNoSignalingPairingBox
end GroupApproximation
