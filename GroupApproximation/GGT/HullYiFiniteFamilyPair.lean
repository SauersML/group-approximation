import GroupApproximation.GGT.HullSCFillingNonElementary

/-!
# Hull's finite-family `yi` theorem contains the pair theorem

The canonical-quotient lane needs Hull's printed all-`m` form, while the
Fournier--Facio suitability reduction only needs two elements.  This file
makes the specialization at `m = 2` literal, so those two manuscript lanes
share one exact source leaf.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry

universe u

/-- Hull's printed finite-family `yi` statement implies its two-element form
without any additional geometric input. -/
theorem yiSuitablePair_of_finiteFamily
    (hyi : YiSuitableFiniteFamily.{u}) : YiSuitablePair.{u} := by
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hgnc, hgcyc⟩ := hyi A hN 2
  let f : Bool → G
    | false => g 0
    | true => g 1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b
    · exact hgN 0
    · exact hgN 1
  · intro b
    cases b
    · exact hglox 0
    · exact hglox 1
  · intro c p q hp hq
    have hne : (0 : Fin 2) ≠ 1 := by decide
    simpa only [f, inv_inv] using
      hgnc (0 : Fin 2) 1 hne p q hp hq c⁻¹
  · intro b
    cases b
    · exact hgcyc 0
    · exact hgcyc 1

end HullSC
end GroupApproximation
