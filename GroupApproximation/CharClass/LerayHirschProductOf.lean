import GroupApproximation.CharClass.CohomologyChartRankTwoInterfaceOf
import GroupApproximation.CharClass.LerayHirschProduct
import GroupApproximation.CharClass.LerayHirschColumnPack

/-!
# Rank-two Leray–Hirsch for a trivial `ℂP^1`-bundle, over a field

The coefficient-generic form of `LerayHirschProduct.bijective_lhSum_cpProd`, against the pullback
of an arbitrary nonzero class `hfib ∈ H^2(ℂP^1; K)`, and its free-module form.

`hasFreeTuple_of_bijective` is the converse of `LerayHirschColumnPack.bijective_lhSum_of_freeTuple`:
`lhDomainOf` is the subgroup cut out by the side condition and `lhSum` is the sum, so bijectivity
in every degree is the free-module statement.  With it the rank-two free tuple needs no ring of
`ℂP^d` at all, which is what lets compact Leray–Hirsch at rank two, and through it the Gysin ring
of `ℂP^d` over `K`, run before the general ladder.

## Main declarations

* `LH.hasFreeTuple_of_bijective` — bijectivity is the free-module statement.
* `LH.bijective_lhSum_cpProdOf` — **rank-two Leray–Hirsch for `U × ℂP^1 → U`, over `K`**.
* `LH.hasFreeTuple_cpProd_zeroOf` — the same, as a free tuple at the chart step's index shape.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-- **Bijectivity of the Leray–Hirsch combination in every degree is the free-module statement.** -/
theorem hasFreeTuple_of_bijective {K : Type} [CommRing K] {X P : TopCat.{0}} (π : P ⟶ X)
    (ξ : Hmod K P 2) (r : ℕ) (h : ∀ n, Function.Bijective (lhSum π ξ r n)) :
    HasFreeTuple π ξ r := by
  intro n
  refine ⟨fun z => ?_, fun a hside hzero => ?_⟩
  · obtain ⟨c, hc⟩ := (h n).2 z
    exact ⟨(c : (i : Fin r) → Hmod K X (n - 2 * (i : ℕ))), c.2, by rw [← hc, lhSum_apply]⟩
  · have h0 : lhSum π ξ r n ⟨a, hside⟩ = lhSum π ξ r n 0 := by
      rw [lhSum_apply, map_zero]
      exact hzero
    have hc := (h n).1 h0
    intro i
    exact congrArg
      (fun c : lhDomainOf K X r n => (c : (j : Fin r) → Hmod K X (n - 2 * (j : ℕ))) i) hc

/-- **Rank-two Leray–Hirsch for the trivial `ℂP^1`-bundle over an arbitrary base, over `K`.**
The powers `1, ξ` of the pullback of any nonzero `hfib` are a basis of the cohomology of the
product over that of the base, in every degree. -/
theorem bijective_lhSum_cpProdOf (K : Type) [Field K] (U : Type) [TopologicalSpace U]
    (hfib : Hmod K (CPtop 1) 2) (hfib0 : hfib ≠ 0) (n : ℕ) :
    Function.Bijective (lhSum (KnCP.cpPrU U 0) (pull (KnCP.cpPrCP U 0) 2 hfib) 2 n) :=
  bijective_lhSum_two (KnCP.cpPrU U 0) (pull (KnCP.cpPrCP U 0) 2 hfib)
    (KnCP.lhLowOf K U) (KnCP.lhSurjOf K U hfib hfib0) (KnCP.lhUniqOf K U hfib hfib0) n

/-- **The rank-two free tuple over `K`**, unconditionally, at the index shape the chart step
takes for its `hfree` at `r = 1`. -/
theorem hasFreeTuple_cpProd_zeroOf (K : Type) [Field K] (U : Type) [TopologicalSpace U]
    (hfib : Hmod K (CPtop 1) 2) (hfib0 : hfib ≠ 0) :
    HasFreeTuple (KnCP.cpFst U 1) (pull (KnCP.cpSnd U 1) 2 hfib) 2 :=
  hasFreeTuple_of_bijective _ _ 2 (bijective_lhSum_cpProdOf K U hfib hfib0)

end

end LH
end CharClass
end GroupApproximation
