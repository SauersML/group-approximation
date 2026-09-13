import GroupApproximation.ThompsonOre.ConjugateAbsorption
import GroupApproximation.ThompsonOre.NestedSupports

/-!
# Item 2 of Guba's Question 3.20 from nested conjugates and Theorem 3.18

This file puts `NestedSupports` and `ConjugateAbsorption` together on abstract data. The data
are a group `G` with elements `x0` and `x1` and a subgroup `H` such that:
* `x1 ∈ H`, and `e : H ≃* G` with `e x1 = x0`;
* conjugates of `H` are nested;
* V. Guba's Theorem 3.18 holds for `x0`.

Item 1 (`exists_common_right_multiple_of_nested`) gives nonzero common right multiples of the
binomials `1 - g` for `g ∈ CPlus x0 x1`. `one_sub_solution_of_common_multiples` absorbs the
support of `b`. With `K[G]` a domain, for every `b` the equation `(1 - x1) u = b v` has a
solution with `(u, v) ≠ (0, 0)`, and for `b ≠ 0` a solution with `b v ≠ 0`.

In Thompson's group `F`, `H` is the copy `F_[1/2,1]` and `e` is the affine rescaling.
-/

namespace GroupApproximation.ThompsonOre

open MonoidAlgebra

variable {K G : Type*} [Ring K] [Group G]

/-- **Item 2 of Guba's Question 3.20 on the abstract data.** If `x1 ∈ H`, `e : H ≃* G` sends
`x1` to `x0`, conjugates of `H` are nested, Theorem 3.18 holds for `x0`, and `K[G]` has no zero
divisors, then for every `b` the equation `(1 - x1) u = b v` has a solution with
`(u, v) ≠ (0, 0)`, and for `b ≠ 0` a solution with `b v ≠ 0`. -/
theorem one_sub_solution_of_nested [Nontrivial K] [NoZeroDivisors (MonoidAlgebra K G)]
    (x0 x1 : G) (H : Subgroup G) (hx1 : x1 ∈ H) (e : H ≃* G) (he : e ⟨x1, hx1⟩ = x0)
    (h318 : ∀ b : MonoidAlgebra K G, b ≠ 0 → ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G x0) * u)
    (hchain : ∀ c : G, (∀ f ∈ H, c * f * c⁻¹ ∈ H) ∨ (∀ f ∈ H, c⁻¹ * f * c ∈ H))
    (b : MonoidAlgebra K G) :
    (∃ u v : MonoidAlgebra K G, (u ≠ 0 ∨ v ≠ 0) ∧ (1 - of K G x1) * u = b * v) ∧
      (b ≠ 0 → ∃ u v : MonoidAlgebra K G, b * v ≠ 0 ∧ (1 - of K G x1) * u = b * v) :=
  one_sub_solution_of_common_multiples x0 x1
    (fun s hs => exists_common_right_multiple_of_nested x0 x1 H hx1 e he h318 hchain s hs) b

end GroupApproximation.ThompsonOre
