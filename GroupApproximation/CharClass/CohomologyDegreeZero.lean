import GroupApproximation.CharClass.CohomologyBasic
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0

/-!
# Degree zero: the class map is injective, and the unit is nonzero

In the `ℕ`-indexed cochain complex degree `0` has no predecessor, so the
differential into degree `0` is zero and `H^0` **is** the group of `0`-cocycles:
`cocycleClass` is injective there.  Consequently the unit class `1 ∈ H^0(X; F₂)`
is nonzero as soon as `X` has a point, because the unit cochain takes the value
`1` on the `0`-simplex sitting at that point.

That is the fact a computation of `H^*(ℂP^n; F₂)` needs in order to know that the
restriction `H^0(U) → H^0(U ∩ V)` of a two-open cover is surjective: over `F₂`
both groups are lines, restriction sends `1` to `1` by `pull_one`, and a map
hitting a nonzero element of a two-element group is onto.

## Main declarations

* `cocycleClass_zero_injective`
* `one_ne_zero_cohZero`
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **In degree zero the class map is injective.**  The differential into degree
`0` is zero, so `homologyπ` is an isomorphism there. -/
theorem cocycleClass_zero_injective (X : TopCat.{0})
    (φ : singularCochainGroup (ZMod 2) X 0) (hφ : cochainCoboundary (ZMod 2) X 0 φ = 0)
    (h : cocycleClass X 0 φ hφ = 0) : φ = 0 := by
  haveI : IsIso ((cochainCxZMod2 X).homologyπ 0) :=
    (cochainCxZMod2 X).isIso_homologyπ 0 0 (by simp [ComplexShape.prev])
      ((cochainCxZMod2 X).shape 0 0 (by simp))
  have hinj : Function.Injective ((cochainCxZMod2 X).homologyπ 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hcyc : (cochainCxZMod2 X).cyclesMk φ 1 (ComplexShape.next_eq' _ rfl) hφ = 0 :=
    hinj (by rw [map_zero]; exact h)
  have h2 : ((cochainCxZMod2 X).iCycles 0).hom
      ((cochainCxZMod2 X).cyclesMk φ 1 (ComplexShape.next_eq' _ rfl) hφ) = φ :=
    iCycles_cyclesMk X 0 φ hφ
  rw [hcyc, map_zero] at h2
  exact h2.symm

/-- **The unit class is nonzero.**  For a nonempty space the class
`1 ∈ H^0(X; F₂)` does not vanish. -/
theorem one_ne_zero_cohZero (X : TopCat.{0}) [Nonempty X] : one X ≠ (0 : Hmod2 X 0) := by
  intro h
  rw [one_eq_cocycleClass] at h
  have h0 := cocycleClass_zero_injective X _ (cochainCoboundary_cochainOne X) h
  have hev : cochainEval 0 (cochainOne (R := ZMod 2) (Z := X))
      (pointSimplex X (Classical.arbitrary X)) = 0 := by
    rw [h0]
    exact cochainEval_zero 0 _
  rw [cochainOne_eval] at hev
  exact one_ne_zero hev

end

end GroupApproximation.CharClass
