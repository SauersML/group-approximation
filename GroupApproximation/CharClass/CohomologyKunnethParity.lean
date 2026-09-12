import GroupApproximation.CharClass.CohomologyKunnethDecomp

/-!
# Parity consequences of the Künneth decomposition with a sphere factor

Two statements that `cc-thom`'s projective-space induction needs.  Both are
immediate from `kunneth_decomposition` and `kunneth_low` once the degrees are
counted, and neither needs the mutual induction they were expected to need: the
decomposition already produces both coefficients in named degrees, so the parity
of those degrees settles the matter.

* **(L)** if the base has no odd cohomology and the sphere is odd dimensional,
  every even-degree class of the product is pulled back from the base;
* **(M)** if the base has no odd cohomology and the sphere is even dimensional,
  neither does the product.

## Main results

* `KnHemi.even_pulled_back_of_odd_sphere`
* `KnHemi.eq_zero_odd_of_even_sphere`, `KnHemi.isZero_odd_prod_sphere`
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- The hypothesis "no odd cohomology", in the form the consumers state it. -/
def NoOddCohomology (A : Type) [TopologicalSpace A] : Prop :=
  ∀ j : ℕ, Odd j → IsZero (Hmod2 (TopCat.of A) j)

theorem eq_zero_of_noOdd {A : Type} [TopologicalSpace A] (h : NoOddCohomology A)
    {j : ℕ} (hj : Odd j) (c : Hmod2 (TopCat.of A) j) : c = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero (h j hj)
  exact Subsingleton.elim _ _

/-- **(L)** With no odd cohomology on the base and an odd-dimensional sphere, every
even-degree class of the product is pulled back from the base. -/
theorem even_pulled_back_of_odd_sphere (A : Type) [TopologicalSpace A] (n : ℕ)
    (hn : 1 ≤ n) (hA : NoOddCohomology A) (hnodd : Odd n) (m : ℕ) (hm : Even m)
    (z : Hmod2 (TopCat.of (A × Sphere n)) m) :
    ∃ a : Hmod2 (TopCat.of A) m, z = pull (knPrY A n) m a := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · exact kunneth_low A n m hlt z
  · obtain ⟨m', hm'⟩ : ∃ m', n + m' = m := ⟨m - n, by omega⟩
    obtain ⟨a, b, hz⟩ := kunneth_decomposition A n hn m m' hm' z
    have hodd' : Odd m' := by
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hnodd
      rw [Nat.even_iff] at hm
      omega
    refine ⟨a, ?_⟩
    rw [hz, eq_zero_of_noOdd hA hodd' b, pull_zero, cup_zero, cohCast_zero, add_zero]

/-- **(M)** With no odd cohomology on the base and an even-dimensional sphere, the
product has no odd cohomology either. -/
theorem eq_zero_odd_of_even_sphere (A : Type) [TopologicalSpace A] (n : ℕ)
    (hn : 1 ≤ n) (hA : NoOddCohomology A) (hneven : Even n) (m : ℕ) (hm : Odd m)
    (z : Hmod2 (TopCat.of (A × Sphere n)) m) : z = 0 := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · obtain ⟨a, ha⟩ := kunneth_low A n m hlt z
    rw [ha, eq_zero_of_noOdd hA hm a, pull_zero]
  · obtain ⟨m', hm'⟩ : ∃ m', n + m' = m := ⟨m - n, by omega⟩
    obtain ⟨a, b, hz⟩ := kunneth_decomposition A n hn m m' hm' z
    have hodd' : Odd m' := by
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hm
      rw [Nat.even_iff] at hneven
      omega
    rw [hz, eq_zero_of_noOdd hA hm a, eq_zero_of_noOdd hA hodd' b, pull_zero,
      pull_zero, cup_zero, cohCast_zero, add_zero]

theorem isZero_odd_prod_sphere (A : Type) [TopologicalSpace A] (n : ℕ) (hn : 1 ≤ n)
    (hA : NoOddCohomology A) (hneven : Even n) (m : ℕ) (hm : Odd m) :
    IsZero (Hmod2 (TopCat.of (A × Sphere n)) m) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun z w => ?_⟩
  rw [eq_zero_odd_of_even_sphere A n hn hA hneven m hm z,
    eq_zero_odd_of_even_sphere A n hn hA hneven m hm w]

/-- **(M) as a `NoOddCohomology` statement**, so it chains. -/
theorem noOddCohomology_prod_sphere (A : Type) [TopologicalSpace A] (n : ℕ)
    (hn : 1 ≤ n) (hA : NoOddCohomology A) (hneven : Even n) :
    NoOddCohomology (A × Sphere n) :=
  fun j hj => isZero_odd_prod_sphere A n hn hA hneven j hj

end KnHemi

end

end GroupApproximation.CharClass
