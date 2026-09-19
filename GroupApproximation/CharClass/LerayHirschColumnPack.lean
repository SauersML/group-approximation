import GroupApproximation.CharClass.LerayHirschPeelClosed

/-!
# The free module, repackaged into the column shape

`cc-cohom-api` produces the free-module statement as plain tuples with a vanishing
side condition; `LHOver` and the ladder consume it as `lhSum` on `lhDomain`.  This
file is the conversion, and it is a repackaging rather than an argument: `lhDomain`
is by definition the subgroup cut out by that very side condition, and `lhSum` is by
definition that very sum.

The side condition is not decoration.  Without it the uniqueness half is false: for
an index with `2i > n` the term vanishes for every coefficient, so those components
are free parameters the sum cannot see, and the coefficient group there is `H⁰(U)`
rather than zero.  That is a different failure from the one that killed one-step
uniqueness — it bites at small degree with the rank fixed, rather than at large
degree — and it is why the statement is asked for in this shape.

## Main declarations

* `HasFreeTuple` — the free-module statement, in the producer's vocabulary.
* `bijective_lhSum_of_freeTuple` — **the column shape**, which is what `LHOver` takes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- **The free-module statement**, as plain tuples with the vanishing side
condition.  Stated in the producer's vocabulary so that nothing on their side needs
`lhDomain`. -/
def HasFreeTuple (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) : Prop :=
  ∀ n : ℕ,
    (∀ z : Hmod2 P n, ∃ a : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ)),
        (∀ i : Fin r, n < 2 * (i : ℕ) → a i = 0)
          ∧ z = ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i))
    ∧ (∀ a : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ)),
        (∀ i : Fin r, n < 2 * (i : ℕ) → a i = 0) →
        (∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i)) = 0 → ∀ i : Fin r, a i = 0)

/-- **The column shape.**  `lhDomain` is the subgroup the side condition cuts out and
`lhSum` is the sum, so this is a repackaging. -/
theorem bijective_lhSum_of_freeTuple (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (h : HasFreeTuple π ξ r) (n : ℕ) : Function.Bijective (lhSum π ξ r n) := by
  constructor
  · intro c c' hcc
    have hzero : lhSum π ξ r n (c - c') = 0 := by
      rw [map_sub, hcc, sub_self]
    have hmem : ∀ i : Fin r, n < 2 * (i : ℕ) →
        ((c - c' : lhDomain X r n) : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i = 0 := by
      intro i hi
      show (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
          - (c' : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i = 0
      rw [c.2 i hi, c'.2 i hi, sub_self]
    have hall := (h n).2 _ hmem (by rw [← lhSum_apply]; exact hzero)
    refine Subtype.ext (funext fun i => ?_)
    have hi := hall i
    show (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
        = (c' : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
    have : (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i
        - (c' : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ))) i = 0 := hi
    exact sub_eq_zero.mp this
  · intro z
    obtain ⟨a, ha0, haz⟩ := (h n).1 z
    exact ⟨⟨a, ha0⟩, by rw [lhSum_apply]; exact haz.symm⟩

end

end LH
end CharClass
end GroupApproximation
