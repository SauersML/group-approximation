import GroupApproximation.CharClass.LerayHirschShiftTerm
import GroupApproximation.CharClass.LerayHirschRankTwo

/-!
# The ladder's spanning half, by peeling

Leray–Hirsch at general rank is a downward induction on the degree.  A class of
degree at least two is one pullback plus the generator cupped with something two
degrees down; recurse on that; and put the peel back with `lhTerm_succ`.  Below
degree two there is nothing to peel, and the pullback is already onto.

Two hypotheses carry the geometry, both stated in the shape `cc-cohom-api`'s
`KnCP` layer produces them.  `HasPeel` is `cpSplit_closed`, the projective-factor
Künneth in its peeling form.  `HasLowSurj` is the floor, which is fibre
connectivity rather than Künneth and so is not visible to the peel.

The summation range is `n + 1` rather than the sharp `n / 2 + 1`.  Terms past the
sharp bound vanish anyway, and carrying the loose bound removes every division
identity from the induction; the sharp column is recovered later, where the rank
truncation is done with `cupPowE_eq_zero_of_gt`.

## Main declarations

* `HasPeel`, `HasLowSurj` — the two inputs.
* `exists_col` — **every class is a column**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- The projective-factor Künneth in peeling form. -/
def HasPeel (π : P ⟶ X) (ξ : Hmod2 P 2) : Prop :=
  ∀ (m : ℕ) (z : Hmod2 P (2 + m)),
    ∃ (a : Hmod2 X (2 + m)) (y : Hmod2 P m), z = pull π (2 + m) a + cup ξ y

/-- The floor: below degree two the pullback is already onto. -/
def HasLowSurj (π : P ⟶ X) : Prop :=
  ∀ n : ℕ, n < 2 → Function.Surjective (pull π n)

/-- Cupping with the class and transporting the degree pass through a sum. -/
theorem cohCast_cup_sum (ξ : Hmod2 P 2) (m : ℕ) (s : Finset ℕ)
    (f : ℕ → Hmod2 P m) :
    cohCast (Nat.add_comm 2 m) (cup ξ (∑ i ∈ s, f i))
      = ∑ i ∈ s, cohCast (Nat.add_comm 2 m) (cup ξ (f i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, cup_zero, cohCast_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cup_add_right, cohCast_add, ih]

/-- **Every class is a column.**  The spanning half of Leray–Hirsch at general
rank, over the two inputs. -/
theorem exists_col (π : P ⟶ X) (ξ : Hmod2 P 2)
    (hlow : HasLowSurj π) (hpeel : HasPeel π ξ) :
    ∀ (n : ℕ) (z : Hmod2 P n),
      ∃ c : (i : ℕ) → Hmod2 X (n - 2 * i),
        z = ∑ i ∈ Finset.range (n + 1), lhTerm π ξ n i (c i) := by
  have low : ∀ (n : ℕ), n < 2 → ∀ z : Hmod2 P n,
      ∃ c : (i : ℕ) → Hmod2 X (n - 2 * i),
        z = ∑ i ∈ Finset.range (n + 1), lhTerm π ξ n i (c i) := by
    intro n hn z
    obtain ⟨a, ha⟩ := hlow n hn z
    refine ⟨fun i => match i with | 0 => a | (_ + 1) => 0, ?_⟩
    match n, hn with
    | 0, _ =>
      rw [Finset.sum_range_one, lhTerm_zero_index]
      exact ha.symm
    | 1, _ =>
      rw [Finset.sum_range_succ, Finset.sum_range_one, lhTerm_zero_index,
        lhTerm_of_gt π ξ (by omega : ¬ 2 * 1 ≤ 1), add_zero]
      exact ha.symm
  have key : ∀ n : ℕ,
      (∀ z : Hmod2 P n, ∃ c : (i : ℕ) → Hmod2 X (n - 2 * i),
        z = ∑ i ∈ Finset.range (n + 1), lhTerm π ξ n i (c i))
      ∧ (∀ z : Hmod2 P (n + 1), ∃ c : (i : ℕ) → Hmod2 X (n + 1 - 2 * i),
        z = ∑ i ∈ Finset.range (n + 1 + 1), lhTerm π ξ (n + 1) i (c i)) := by
    intro n
    induction n with
    | zero => exact ⟨low 0 (by omega), low 1 (by omega)⟩
    | succ m ihm =>
      refine ⟨ihm.2, ?_⟩
      intro z
      obtain ⟨a, y, hz⟩ := hpeel m (cohCast (by omega : m + 1 + 1 = 2 + m) z)
      obtain ⟨c, hy⟩ := ihm.1 y
      refine ⟨fun i => match i with
        | 0 => cohCast (by omega : 2 + m = m + 1 + 1 - 2 * 0) a
        | (j + 1) => cohCast (by omega : m - 2 * j = m + 1 + 1 - 2 * (j + 1)) (c j), ?_⟩
      have hy' : y = ∑ j ∈ Finset.range (m + 2), lhTerm π ξ m j (c j) := by
        rw [Finset.sum_range_succ, ← hy,
          lhTerm_of_gt π ξ (by omega : ¬ 2 * (m + 1) ≤ m), add_zero]
      rw [Finset.sum_range_succ']
      have hshift : ∀ j : ℕ,
          lhTerm π ξ (m + 1 + 1) (j + 1)
              (cohCast (by omega : m - 2 * j = m + 1 + 1 - 2 * (j + 1)) (c j))
            = cohCast (Nat.add_comm 2 m) (cup ξ (lhTerm π ξ m j (c j))) := fun j =>
        lhTerm_succ π ξ m j (c j)
      rw [Finset.sum_congr rfl (fun j _ => hshift j), ← cohCast_cup_sum, ← hy',
        lhTerm_zero_index]
      have hz' : z = cohCast (Nat.add_comm 2 m) (pull π (2 + m) a + cup ξ y) := by
        rw [← hz]
        simp only [cohCast_cohCast, cohCast_self]
      rw [hz', cohCast_add, pull_cohCast]
      exact add_comm _ _
  exact fun n => (key n).1

end

end LH
end CharClass
end GroupApproximation
