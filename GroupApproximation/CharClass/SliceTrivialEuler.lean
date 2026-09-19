import GroupApproximation.CharClass.ChernSplitFactor
import GroupApproximation.CharClass.CohomologyContractible

/-!
# A constant line has vanishing Euler class

Three of the summands of `V` are constant lines, and their contribution to the
split relation has to be a root of zero, so that the corresponding factors of the
slice polynomial are `1` rather than linear factors left standing.

A constant bundle has a constant classifying map, so it factors through a point,
and a point has no second cohomology.  That is the whole argument; the only care
needed is that the classifying map of the *pushforward* is the one that has to be
seen as constant, since `lineEulerOf` is defined after pushing the index forward.

## Main declarations

* `lineEulerOf_const` — **a constant line has zero Euler class.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn
open GroupApproximation.CharClass.LH

noncomputable section

/-- **A constant line has vanishing Euler class.**  Its classifying map is
constant, so it factors through a point. -/
theorem lineEulerOf_const {X : Type} [TopologicalSpace X] [Nonempty X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (L : Bundle X ι) (hL : ∀ x, (L x).trace = 1)
    (hconst : ∀ x y : X, L x = L y) : lineEulerOf L hL = 0 := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  set P := pushforward (tautEmbOf ι) (tautEmbOf_injective ι) L with hPdef
  set hPtr := trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) L hL with hPtrdef
  have hPconst : ∀ x : X, P x = P x₀ := by
    intro x
    show coordIncl (tautEmbOf ι) * L x * (coordIncl (tautEmbOf ι))ᴴ
      = coordIncl (tautEmbOf ι) * L x₀ * (coordIncl (tautEmbOf ι))ᴴ
    rw [hconst x x₀]
  show eulerOfBundle (show 1 ≤ 1 + tautCardOf ι by omega) P hPtr = 0
  refine eulerOfBundle_eq_zero_of_factors (show 1 ≤ 1 + tautCardOf ι by omega) P hPtr
    (TopCat.ofHom ⟨fun _ => (), continuous_const⟩)
    (TopCat.ofHom ⟨fun _ => classifyOne P hPtr x₀, continuous_const⟩) ?_
    (fun a => cohomology_eq_zero_of_contractible Unit 2 (by omega) a)
  exact TopCat.hom_ext (ContinuousMap.ext fun x => Subtype.ext (hPconst x))

end

end CharClass
end GroupApproximation
