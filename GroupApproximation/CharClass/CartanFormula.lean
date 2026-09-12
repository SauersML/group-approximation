import GroupApproximation.CharClass.CartanReindex
import GroupApproximation.CharClass.SteenrodCartanTotal

/-!
# The Cartan formula

Everything assembles here.  The comparison of the two composites, evaluated
against `α ⊗ β ⊗ α ⊗ β`, becomes an identity of classes; the left side is the
square of the cup product and the right side, reindexed, is the Cartan sum.

## Main results

* `cartan_generic` — the formula when the total degree is positive.
* `cartanOf_holds` — **`CartanOf X`, for every space.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

theorem cartanRhsSum_eq (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (d e : ℕ) :
    cartanRhsSum X p q α β d e
      = ∑ j' ∈ Finset.range (e + 1),
          padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
            (cupSqTerm X p q α β e j') := rfl

variable {X : TopCat.{0}} {p q : ℕ}
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
  (hα : cochainCoboundary (ZMod 2) X p α = 0)
  (hβ : cochainCoboundary (ZMod 2) X q β = 0)

/-- **The Cartan formula on cocycle representatives**, when the total degree is
positive. -/
theorem cartan_generic (n : ℕ) (hn : n ≤ p + q) (hpos : 1 ≤ n + (p + q)) :
    TotalH.of X (n + (p + q))
        (Sq n (cup (cocycleClass X p α hα) (cocycleClass X q β hβ)))
      = ∑ i ∈ Finset.range (n + 1), cartanTermR α β hα hβ n i := by
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = n + (p + q) := ⟨n + (p + q) - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = p + q + (p + q) := ⟨p + q + (p + q) - 1, by omega⟩
  have hdn : d < m + 1 := by omega
  have he : d + 1 + (p + q - n) = m + 1 := by omega
  have hcls := cartan_class α β hα hβ m n d (p + q - n) hm hn hd he hdn
  have hcup : cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q α β) = 0 :=
    cochainCupZMod2_respects_cocycles p q α β hα hβ
  -- the left-hand side
  have hL : TotalH.of X (d + 1)
      (cocycleClass X (d + 1)
        (cochainCast hd.symm (sqCochain (p + q) n (cochainCup p q α β)))
        (cast_sqCochain_cocycle α β hα hβ n d hd))
      = TotalH.of X (n + (p + q))
          (Sq n (cup (cocycleClass X p α hα) (cocycleClass X q β hβ))) := by
    rw [cocycleClass_cochainCast X hd.symm _
        (sqCochain_cocycle (p + q) n (cochainCup p q α β) hcup),
      Steenrod.of_cohCast, cup_mk α hα β hβ, Sq_mk n (p + q) (cochainCup p q α β) hcup]
  -- the right-hand side
  have hR : TotalH.of X (d + 1)
      (cocycleClass X (d + 1) (cartanRhsCochain X p q α β d (p + q - n))
        (cartanRhs_cocycle α β hα hβ m n d (p + q - n) hm hn hd he hdn))
      = ∑ j' ∈ Finset.range (p + q - n + 1), cartanTermL α β hα hβ d (p + q - n) j' := by
    have hrhs2 : cochainCoboundary (ZMod 2) X (d + 1)
        (cartanRhsSum X p q α β d (p + q - n)) = 0 := by
      rw [← cartanRhsCochain_eq_sum]
      exact cartanRhs_cocycle α β hα hβ m n d (p + q - n) hm hn hd he hdn
    refine Eq.trans (congrArg (TotalH.of X (d + 1))
      (cocycleClass_congr X (d + 1) (cartanRhsCochain_eq_sum X p q α β d (p + q - n))
        (cartanRhs_cocycle α β hα hβ m n d (p + q - n) hm hn hd he hdn) hrhs2)) ?_
    refine Eq.trans (congrArg (TotalH.of X (d + 1))
      (cocycleClass_finset_sum X (d + 1) (Finset.range (p + q - n + 1))
        (fun j' => padCochain X (p + p - j' + (q + q - (p + q - n - j'))) (d + 1)
          (cupSqTerm X p q α β (p + q - n) j'))
        (fun j' => padCochain_cocycle X _ (d + 1) _
          (cupSqTerm_cocycle X p q α β hα hβ (p + q - n) j')) hrhs2)) ?_
    exact map_sum _ _ _
  rw [← hL, hcls, hR, cartan_sum_reindex α β hα hβ n d (p + q - n) hn hd rfl]

/-- **The Cartan formula**, for every space. -/
theorem cartanOf_holds (X : TopCat.{0}) : Steenrod.CartanOf X := by
  intro n p q a b
  obtain ⟨α, hα, rfl⟩ := exists_cocycle a
  obtain ⟨β, hβ, rfl⟩ := exists_cocycle b
  by_cases hn : n ≤ p + q
  · by_cases hpos : 1 ≤ n + (p + q)
    · exact cartan_generic α β hα hβ n hn hpos
    · have hn0 : n = 0 := by omega
      have hp0 : p = 0 := by omega
      have hq0 : q = 0 := by omega
      subst hn0
      subst hp0
      subst hq0
      rw [Finset.sum_range_one, Sq_zero, Sq_zero, Sq_zero, Steenrod.of_cohCast,
        Steenrod.of_cohCast, Steenrod.of_cohCast]
      exact TotalH.of_mul X 0 0 _ _
  · rw [Sq_eq_zero_of_lt n (p + q) (by omega), map_zero]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [Finset.mem_range] at hi
    by_cases hip : i ≤ p
    · rw [Sq_eq_zero_of_lt (n - i) q (by omega), map_zero, mul_zero]
    · rw [Sq_eq_zero_of_lt i p (by omega), map_zero, zero_mul]

end

end GroupApproximation.CharClass
