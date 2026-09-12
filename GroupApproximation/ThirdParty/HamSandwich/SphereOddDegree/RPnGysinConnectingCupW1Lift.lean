import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCupFaces

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 3. `w₁` on the back edge -/

/-
**Lift-independence of `w1Value`.** For any singular `1`-simplex `σ` of `RPⁿ`
and any continuous lift `g : Δ¹ → Sⁿ` of its chart, the `w₁` value of `σ` is the
sum of the sheet parities of `g` at the two endpoints.
-/
theorem w1Value_of_lift (n : ℕ) (σ : singularSimplices (TopCat.of (RP n)) 1)
    (g : C(stdSimplex ℝ (Fin 2), Sphere n)) (hg : ∀ x, proj n (g x) = rpChart n 1 σ x) :
    w1Value n σ
      = sheetParity n (g (stdSimplex.vertex 0)) + sheetParity n (g (stdSimplex.vertex 1)) := by
  let L : C(stdSimplex ℝ (Fin 2), Sphere n) :=
    ⟨fun a => simplexLift n 1 σ (ULift.up a), by continuity⟩
  have hL : ∀ a, proj n (L a) = rpChart n 1 σ a := by
    intro a
    have hs := congrFun (simplexLift_spec n 1 σ) (ULift.up a)
    change proj n (simplexLift n 1 σ (ULift.up a)) = _
    calc
      _ = rpCochainSimplexMap n 1 σ (ULift.up a) := hs
      _ = rpChart n 1 σ a := rfl
  have hgMap : (proj n) ∘ g = rpChart n 1 σ :=
    funext fun a => hg a
  have hLMap : (proj n) ∘ L = rpChart n 1 σ :=
    funext fun a => hL a
  rcases proj_lift_dichotomy n g L hgMap hLMap with hglobal | hglobal
  · rw [hglobal]
    rfl
  · rw [hglobal (stdSimplex.vertex 0), hglobal (stdSimplex.vertex 1)]
    unfold w1Value
    rw [sheetParity_neg, sheetParity_neg]
    change _ = (sheetParity n (simplexLift n 1 σ (simplexVertex 1 0)) + 1) +
      (sheetParity n (simplexLift n 1 σ (simplexVertex 1 1)) + 1)
    generalize sheetParity n (simplexLift n 1 σ (simplexVertex 1 0)) = a
    generalize sheetParity n (simplexLift n 1 σ (simplexVertex 1 1)) = b
    revert a b
    decide

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
