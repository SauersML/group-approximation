import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Choose

/-!
# Absorbing conjugates: item 2 of Guba's Question 3.20 from item 1

Let `K` be a ring, `G` a group and `R = K[G]`.  The identity `t (1 - t⁻¹ h t) = (1 - h) t`
shows that if `v` lies in `(1 - t⁻¹ h t) R` for every `t` in the support of `b`, then `b v`
lies in `(1 - h) R`.

So let `C ⊆ G` be closed under conjugation, and suppose every finite subset of `C` has a
nonzero common right multiple of its binomials `1 - g`.  Then for every `h ∈ C` and every `b`,
the equation `(1 - h) u = b v` has a solution with `v ≠ 0`.  If `R` has no zero divisors and
`b ≠ 0`, then also `b v ≠ 0`, that is `(1 - h) R ∩ b R ≠ 0`.

For Thompson's group `F` the set is `CPlus x0 x1`, the union of the conjugacy classes of
`x0^{±1}` and `x1^{±1}`.  Question 3.20 of V. Guba, *Amenability problem for Thompson's group
F: state of the art*, arXiv:2305.07113v4, asks whether `(1 - x1) u = b v` has a non-zero
solution for every `b`.  `one_sub_solution_of_common_multiples` states both readings: a pair
`(u, v) ≠ (0, 0)` for every `b`, and a nonzero common multiple `b v` for every nonzero `b`.

Everything here is group-generic and uses only Mathlib.
-/

namespace GroupApproximation.ThompsonOre

open MonoidAlgebra

section Conj

variable {G : Type*} [Group G]

/-- The union of the conjugacy classes of `x0^{±1}` and `x1^{±1}`. -/
def CPlus (x0 x1 : G) : Set G :=
  {g | IsConj x0 g ∨ IsConj x0⁻¹ g ∨ IsConj x1 g ∨ IsConj x1⁻¹ g}

/-- `CPlus x0 x1` is closed under conjugation. -/
theorem conj_mem_CPlus {x0 x1 g : G} (hg : g ∈ CPlus x0 x1) (t : G) :
    t⁻¹ * g * t ∈ CPlus x0 x1 := by
  have hc : IsConj g (t⁻¹ * g * t) := isConj_iff.mpr ⟨t⁻¹, by rw [inv_inv]⟩
  change IsConj x0 g ∨ IsConj x0⁻¹ g ∨ IsConj x1 g ∨ IsConj x1⁻¹ g at hg
  change IsConj x0 (t⁻¹ * g * t) ∨ IsConj x0⁻¹ (t⁻¹ * g * t) ∨ IsConj x1 (t⁻¹ * g * t) ∨
    IsConj x1⁻¹ (t⁻¹ * g * t)
  rcases hg with hg | hg | hg | hg
  · exact Or.inl (hg.trans hc)
  · exact Or.inr (Or.inl (hg.trans hc))
  · exact Or.inr (Or.inr (Or.inl (hg.trans hc)))
  · exact Or.inr (Or.inr (Or.inr (hg.trans hc)))

theorem left_mem_CPlus (x0 x1 : G) : x0 ∈ CPlus x0 x1 := by
  change IsConj x0 x0 ∨ IsConj x0⁻¹ x0 ∨ IsConj x1 x0 ∨ IsConj x1⁻¹ x0
  exact Or.inl (IsConj.refl x0)

theorem right_mem_CPlus (x0 x1 : G) : x1 ∈ CPlus x0 x1 := by
  change IsConj x0 x1 ∨ IsConj x0⁻¹ x1 ∨ IsConj x1 x1 ∨ IsConj x1⁻¹ x1
  exact Or.inr (Or.inr (Or.inl (IsConj.refl x1)))

end Conj

section GroupRing

variable {K G : Type*} [Ring K] [Group G]

/-- The basic identity `t (1 - t⁻¹ h t) = (1 - h) t`, with a coefficient on `t`. -/
theorem single_mul_one_sub_conj (t h : G) (r : K) :
    single t r * (1 - of K G (t⁻¹ * h * t)) = (1 - of K G h) * single t r := by
  simp [mul_sub, sub_mul, mul_assoc]

/-- If `v ∈ (1 - t⁻¹ h t) R` for every `t` in the support of `b`, then `b v ∈ (1 - h) R`. -/
theorem exists_one_sub_mul_eq_mul_of_forall_conj (h : G) (b v : MonoidAlgebra K G)
    (hv : ∀ t ∈ b.coeff.support, ∃ y, (1 - of K G (t⁻¹ * h * t)) * y = v) :
    ∃ u, (1 - of K G h) * u = b * v := by
  choose! y hy using hv
  refine ⟨∑ t ∈ b.coeff.support, single t (b.coeff t) * y t, ?_⟩
  conv_rhs => rw [← sum_coeff_single b, Finsupp.sum, Finset.sum_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← hy t ht, ← mul_assoc, ← mul_assoc, single_mul_one_sub_conj]

/-- Item 2 from item 1: if `C` is closed under conjugation and every finite subset of `C` has a
nonzero common right multiple of its binomials, then for `h ∈ C` every `b` has a nonzero `v`
with `b v ∈ (1 - h) R`. -/
theorem exists_ne_zero_one_sub_mul_eq_mul (C : Set G)
    (hC : ∀ g ∈ C, ∀ t : G, t⁻¹ * g * t ∈ C)
    (hcommon : ∀ s : Finset G, (∀ g ∈ s, g ∈ C) →
      ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ ∀ g ∈ s, ∃ y, (1 - of K G g) * y = v)
    {h : G} (hh : h ∈ C) (b : MonoidAlgebra K G) :
    ∃ u v : MonoidAlgebra K G, v ≠ 0 ∧ (1 - of K G h) * u = b * v := by
  classical
  obtain ⟨v, hv0, hv⟩ := hcommon (b.coeff.support.image fun t => t⁻¹ * h * t) fun g hg => by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hg
    exact hC h hh t
  obtain ⟨u, hu⟩ := exists_one_sub_mul_eq_mul_of_forall_conj h b v fun t ht =>
    hv _ (Finset.mem_image_of_mem _ ht)
  exact ⟨u, v, hv0, hu⟩

/-- With no zero divisors, a nonzero `b` has a nonzero common right multiple with `1 - h`. -/
theorem exists_mul_ne_zero_one_sub_mul_eq_mul [NoZeroDivisors (MonoidAlgebra K G)] (C : Set G)
    (hC : ∀ g ∈ C, ∀ t : G, t⁻¹ * g * t ∈ C)
    (hcommon : ∀ s : Finset G, (∀ g ∈ s, g ∈ C) →
      ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ ∀ g ∈ s, ∃ y, (1 - of K G g) * y = v)
    {h : G} (hh : h ∈ C) {b : MonoidAlgebra K G} (hb : b ≠ 0) :
    ∃ u v : MonoidAlgebra K G, b * v ≠ 0 ∧ (1 - of K G h) * u = b * v := by
  obtain ⟨u, v, hv0, huv⟩ := exists_ne_zero_one_sub_mul_eq_mul C hC hcommon hh b
  exact ⟨u, v, mul_ne_zero hb hv0, huv⟩

/-- The survey's reading: `(1 - h) u = b v` has a solution `(u, v) ≠ (0, 0)` for every `b`,
including `b = 0`. -/
theorem exists_solution_ne_zero (C : Set G) (hC : ∀ g ∈ C, ∀ t : G, t⁻¹ * g * t ∈ C)
    (hcommon : ∀ s : Finset G, (∀ g ∈ s, g ∈ C) →
      ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ ∀ g ∈ s, ∃ y, (1 - of K G g) * y = v)
    {h : G} (hh : h ∈ C) (b : MonoidAlgebra K G) :
    ∃ u v : MonoidAlgebra K G, (u ≠ 0 ∨ v ≠ 0) ∧ (1 - of K G h) * u = b * v := by
  obtain ⟨u, v, hv0, huv⟩ := exists_ne_zero_one_sub_mul_eq_mul C hC hcommon hh b
  exact ⟨u, v, Or.inr hv0, huv⟩

/-- Question 3.20 for `x1`, group-generic, from item 1 for `CPlus x0 x1`: a non-zero solution
`(u, v)` for every `b`, and a nonzero common multiple `b v` for every nonzero `b`. -/
theorem one_sub_solution_of_common_multiples [NoZeroDivisors (MonoidAlgebra K G)] (x0 x1 : G)
    (hcommon : ∀ s : Finset G, (∀ g ∈ s, g ∈ CPlus x0 x1) →
      ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ ∀ g ∈ s, ∃ y, (1 - of K G g) * y = v)
    (b : MonoidAlgebra K G) :
    (∃ u v : MonoidAlgebra K G, (u ≠ 0 ∨ v ≠ 0) ∧ (1 - of K G x1) * u = b * v) ∧
      (b ≠ 0 → ∃ u v : MonoidAlgebra K G, b * v ≠ 0 ∧ (1 - of K G x1) * u = b * v) :=
  ⟨exists_solution_ne_zero (CPlus x0 x1) (fun _ hg t => conj_mem_CPlus hg t) hcommon
      (right_mem_CPlus x0 x1) b,
    fun hb => exists_mul_ne_zero_one_sub_mul_eq_mul (CPlus x0 x1)
      (fun _ hg t => conj_mem_CPlus hg t) hcommon (right_mem_CPlus x0 x1) hb⟩

end GroupRing

end GroupApproximation.ThompsonOre
