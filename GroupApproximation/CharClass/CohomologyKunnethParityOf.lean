import GroupApproximation.CharClass.CohomologyKunnethDecompOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Parity consequences of the Künneth decomposition with a sphere factor, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethParity` with coefficients in a field `K`.  Both statements are
read off `kunneth_decompositionOf` and `kunneth_lowOf` by counting degrees; nothing uses the
characteristic.

* **(L)** if the base has no odd cohomology and the sphere is odd dimensional, every even-degree
  class of the product is pulled back from the base;
* **(M)** if the base has no odd cohomology and the sphere is even dimensional, neither does the
  product.

## Main results

* `KnHemi.NoOddCohomologyOf`, `KnHemi.eq_zero_of_noOddOf`.
* `KnHemi.even_pulled_back_of_odd_sphereOf`.
* `KnHemi.eq_zero_odd_of_even_sphereOf`, `KnHemi.isZero_odd_prod_sphereOf`,
  `KnHemi.noOddCohomology_prod_sphereOf`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- The hypothesis "no odd cohomology with coefficients in `K`". -/
def NoOddCohomologyOf (K : Type) [CommRing K] (A : Type) [TopologicalSpace A] : Prop :=
  ∀ j : ℕ, Odd j → IsZero (Hmod K (TopCat.of A) j)

theorem eq_zero_of_noOddOf {K : Type} [CommRing K] {A : Type} [TopologicalSpace A]
    (h : NoOddCohomologyOf K A) {j : ℕ} (hj : Odd j) (c : Hmod K (TopCat.of A) j) : c = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero (h j hj)
  exact Subsingleton.elim _ _

/-- **(L) over `K`.**  With no odd cohomology on the base and an odd-dimensional sphere, every
even-degree class of the product is pulled back from the base. -/
theorem even_pulled_back_of_odd_sphereOf (K : Type) [Field K] (A : Type) [TopologicalSpace A]
    (n : ℕ) (hn : 1 ≤ n) (hA : NoOddCohomologyOf K A) (hnodd : Odd n) (m : ℕ) (hm : Even m)
    (z : Hmod K (TopCat.of (A × Sphere n)) m) :
    ∃ a : Hmod K (TopCat.of A) m, z = pull (knPrY A n) m a := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · exact kunneth_lowOf K A n m hlt z
  · obtain ⟨m', hm'⟩ : ∃ m', n + m' = m := ⟨m - n, by omega⟩
    obtain ⟨a, b, hz⟩ := kunneth_decompositionOf K A n hn m m' hm' z
    have hodd' : Odd m' := by
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hnodd
      rw [Nat.even_iff] at hm
      omega
    refine ⟨a, ?_⟩
    rw [hz, eq_zero_of_noOddOf hA hodd' b, pull_zero, cup_zero, CharClass.cohCast_zero, add_zero]

/-- **(M) over `K`.**  With no odd cohomology on the base and an even-dimensional sphere, the
product has no odd cohomology either. -/
theorem eq_zero_odd_of_even_sphereOf (K : Type) [Field K] (A : Type) [TopologicalSpace A] (n : ℕ)
    (hn : 1 ≤ n) (hA : NoOddCohomologyOf K A) (hneven : Even n) (m : ℕ) (hm : Odd m)
    (z : Hmod K (TopCat.of (A × Sphere n)) m) : z = 0 := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · obtain ⟨a, ha⟩ := kunneth_lowOf K A n m hlt z
    rw [ha, eq_zero_of_noOddOf hA hm a, pull_zero]
  · obtain ⟨m', hm'⟩ : ∃ m', n + m' = m := ⟨m - n, by omega⟩
    obtain ⟨a, b, hz⟩ := kunneth_decompositionOf K A n hn m m' hm' z
    have hodd' : Odd m' := by
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hm
      rw [Nat.even_iff] at hneven
      omega
    rw [hz, eq_zero_of_noOddOf hA hm a, eq_zero_of_noOddOf hA hodd' b, pull_zero,
      pull_zero, cup_zero, CharClass.cohCast_zero, add_zero]

theorem isZero_odd_prod_sphereOf (K : Type) [Field K] (A : Type) [TopologicalSpace A] (n : ℕ)
    (hn : 1 ≤ n) (hA : NoOddCohomologyOf K A) (hneven : Even n) (m : ℕ) (hm : Odd m) :
    IsZero (Hmod K (TopCat.of (A × Sphere n)) m) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun z w => ?_⟩
  rw [eq_zero_odd_of_even_sphereOf K A n hn hA hneven m hm z,
    eq_zero_odd_of_even_sphereOf K A n hn hA hneven m hm w]

/-- **(M) as a `NoOddCohomologyOf` statement**, so it chains. -/
theorem noOddCohomology_prod_sphereOf (K : Type) [Field K] (A : Type) [TopologicalSpace A]
    (n : ℕ) (hn : 1 ≤ n) (hA : NoOddCohomologyOf K A) (hneven : Even n) :
    NoOddCohomologyOf K (A × Sphere n) :=
  fun j hj => isZero_odd_prod_sphereOf K A n hn hA hneven j hj

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.even_pulled_back_of_odd_sphereOf
#audit_axioms KnHemi.noOddCohomology_prod_sphereOf

end GroupApproximation.CharClass
