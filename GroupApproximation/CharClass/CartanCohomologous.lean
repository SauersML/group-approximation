import GroupApproximation.CharClass.SteenrodCupOne

/-!
# Cohomologous cocycles have the same class

The last step of the Cartan extraction is the ordinary one: the two evaluated
cochains differ by a coboundary, so their classes agree.  The two halves of that
already exist — the class of a sum is the sum of the classes, and a coboundary
has zero class — and this file is the one-line combination, in the shape the
extraction consumes, together with the bridge from a pointwise identity between
evaluations to an identity between cochains.

## Main results

* `cocycleClass_add_coboundary` — adding a coboundary does not change the class.
* `cocycleClass_eq_of_add_coboundary` — the same, with the identity supplied as
  a hypothesis rather than built into the statement.
* `cochain_eq_of_cochainEval` — equal on every simplex means equal.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

/-- **Adding a coboundary does not change the cohomology class.** -/
theorem cocycleClass_add_coboundary (X : TopCat.{0}) (m : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X (m + 1))
    (hψ : cochainCoboundary (ZMod 2) X (m + 1) ψ = 0)
    (η : singularCochainGroup (ZMod 2) X m)
    (hsum : cochainCoboundary (ZMod 2) X (m + 1)
      (ψ + cochainCoboundary (ZMod 2) X m η) = 0) :
    cocycleClass X (m + 1) (ψ + cochainCoboundary (ZMod 2) X m η) hsum
      = cocycleClass X (m + 1) ψ hψ := by
  rw [cocycleClass_add X (m + 1) ψ (cochainCoboundary (ZMod 2) X m η) hψ
      (cochainCoboundary_cochainCoboundary X m η) hsum,
    cocycleClass_coboundary_zero, add_zero]

/-- **Cohomologous cocycles have the same class.** -/
theorem cocycleClass_eq_of_add_coboundary (X : TopCat.{0}) (m : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X (m + 1))
    (hφ : cochainCoboundary (ZMod 2) X (m + 1) φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X (m + 1) ψ = 0)
    (η : singularCochainGroup (ZMod 2) X m)
    (h : φ = ψ + cochainCoboundary (ZMod 2) X m η) :
    cocycleClass X (m + 1) φ hφ = cocycleClass X (m + 1) ψ hψ := by
  subst h
  exact cocycleClass_add_coboundary X m ψ hψ η hφ

/-- Two cochains agreeing on every simplex are equal.  This is the bridge from
the evaluated comparison, which is a pointwise identity, to an identity between
cochains. -/
theorem cochain_eq_of_cochainEval (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n)
    (h : ∀ σ : singularSimplices X n, cochainEval n φ σ = cochainEval n ψ σ) :
    φ = ψ :=
  cochain_ext h

end

end GroupApproximation.CharClass
