import GroupApproximation.CharClass.LerayHirschBridge
import GroupApproximation.CharClass.GysinFromLerayHirsch
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# Leray–Hirsch at rank two, in the two statements the Gysin step consumes

`GysinData` asks for Leray–Hirsch not as a bijection but as its two halves,
spanning and freeness, and in the concrete form `z = π^*a + (π^*b) ⌣ ξ`.  This
file reads those off the published `LerayHirschGraded` at rank two.

Everything is stated in degree `n + 2` rather than `n`, which is what makes the
computation cast-free: `2 * 0` reduces to `0`, `2 * 1` to `2`, and `n + 2 - 2`
to `n`, so the two summands of the rank-two Leray–Hirsch combination are already
`π^*a` and `(π^*b) ⌣ ξ` on the nose, with every transport an identity.

## Main declarations

* `cupPowE_one` — the first cup power is the class itself.
* `lhSum_two_apply` — the rank-two combination, written out.
* `lh_surj_of_graded`, `lh_uniq_of_graded` — **the two `GysinData` fields**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

theorem cupPowE_one (e : Hmod2 P 2) : cupPowE e 1 = e := by
  show cup (cupPowE e 0) e = e
  rw [cupPowE_zero, one_cup']
  exact cohCast_self _ _

/-- **The rank-two Leray–Hirsch combination, written out.**  No transport survives:
the zeroth summand is the pullback and the first is the pullback cupped with the
class. -/
theorem lhTerm_index_zero (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (a : Hmod2 X (n + 2 - 2 * 0)) : lhTerm π ξ (n + 2) 0 a = pull π (n + 2) a := by
  rw [lhTerm_of_le π ξ (by omega : 2 * 0 ≤ n + 2), cupPowE_zero, cup_one]
  exact cohCast_self _ _

theorem lhTerm_index_one (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (b : Hmod2 X (n + 2 - 2 * 1)) :
    lhTerm π ξ (n + 2) 1 b = cup (pull π n b) ξ := by
  rw [lhTerm_of_le π ξ (by omega : 2 * 1 ≤ n + 2), cupPowE_one]
  exact cohCast_self _ _

/-- **The rank-two Leray–Hirsch combination, written out.**  No transport survives:
the zeroth summand is the pullback and the first is the pullback cupped with the
class. -/
theorem lhSum_two_apply (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (c : lhDomain X 2 (n + 2)) :
    lhSum π ξ 2 (n + 2) c
      = pull π (n + 2)
          ((c : (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 0)
        + cup (pull π n
          ((c : (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 1)) ξ := by
  rw [lhSum_apply, Fin.sum_univ_two]
  show lhTerm π ξ (n + 2) 0
      ((c : (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 0)
    + lhTerm π ξ (n + 2) 1
      ((c : (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 1) = _
  rw [lhTerm_index_zero, lhTerm_index_one]

/-- The rank-two column element with prescribed components.  Nothing is cut out:
in degree `n + 2` both summands are admissible, so the subgroup condition is
vacuous. -/
def colTwo (X : TopCat.{0}) (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n) :
    lhDomain X 2 (n + 2) :=
  ⟨Fin.cases (motive := fun j : Fin 2 => Hmod2 X (n + 2 - 2 * (j : ℕ))) a
      (fun i => cohCast (by
        have h1 := i.2
        have h2 : ((i.succ : Fin 2) : ℕ) = (i : ℕ) + 1 := rfl
        omega) b), by
    intro j hj
    exact absurd hj (by have := j.2; omega)⟩

@[simp] theorem colTwo_zero (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n) :
    ((colTwo X n a b : lhDomain X 2 (n + 2)) :
      (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 0 = a := rfl

@[simp] theorem colTwo_one (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n) :
    ((colTwo X n a b : lhDomain X 2 (n + 2)) :
      (j : Fin 2) → Hmod2 X (n + 2 - 2 * (j : ℕ))) 1 = b := rfl

variable {π : P ⟶ X} {ξ : Hmod2 P 2}

/-- **Leray–Hirsch, spanning half**, in the `GysinData` shape. -/
theorem lh_surj_of_graded (L : LerayHirschGraded π ξ 2) (n : ℕ) (z : Hmod2 P (n + 2)) :
    ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      z = pull π (n + 2) a + cup (pull π n b) ξ := by
  obtain ⟨c, hc⟩ := (bijective_lhSum_of_graded L (n + 2)).2 z
  exact ⟨_, _, by rw [← hc, lhSum_two_apply]⟩

/-- **Leray–Hirsch, freeness half**, in the `GysinData` shape. -/
theorem lh_uniq_of_graded (L : LerayHirschGraded π ξ 2) (n : ℕ)
    (a : Hmod2 X (n + 2)) (b : Hmod2 X n)
    (h : pull π (n + 2) a + cup (pull π n b) ξ = 0) : a = 0 ∧ b = 0 := by
  have hz : lhSum π ξ 2 (n + 2) (colTwo X n a b) = 0 := by
    rw [lhSum_two_apply, colTwo_zero, colTwo_one]
    exact h
  have hc : colTwo X n a b = 0 := by
    refine (bijective_lhSum_of_graded L (n + 2)).1 ?_
    rw [hz, map_zero]
  constructor
  · have h0 := lhDomain_apply_eq hc (0 : Fin 2)
    rwa [colTwo_zero, lhDomain_zero_apply] at h0
  · have h1 := lhDomain_apply_eq hc (1 : Fin 2)
    rwa [colTwo_one, lhDomain_zero_apply] at h1

end

end LH
end CharClass
end GroupApproximation
