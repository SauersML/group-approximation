import GroupApproximation.CharClass.CartanCompBBridge
import GroupApproximation.CharClass.CartanEvalCoboundary

/-!
# The master identity at the packaged second composite

With composite B packaged as a natural transformation and the degree-zero
agreement in hand, the comparison instantiates and the master identity becomes a
statement about two explicit cochains.

The source index is written as a successor from the start.  The coboundary term
lives one degree down, so a statement whose index is a bare `Fin` would need that
index to be a successor at some point anyway, and choosing the spelling once
here removes every later transport of the simplex.

## Main results

* `cartan_master` — **the two composites evaluated, at the packaged B**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **The master identity, at the packaged second composite.**  Evaluated
against `α ⊗ β ⊗ α ⊗ β` for a pair of cocycles, the two composites on a basis
element differ by the coboundary of the homotopy cochain. -/
theorem cartan_master (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n : ℕ) (m : Fin (n + 1)) (σ : singularSimplices X (m.val + 1)) :
    fourEvalF2 X p q α β (n + 1)
        (((compA.app X).f (n + 1)).hom
          (Finsupp.single
            (⟨Fin.succ m, simplexEquiv X (Fin.succ m).val σ⟩ : WSIndex (n + 1) X)
            (1 : GroupRingZ2)))
      = fourEvalF2 X p q α β (n + 1)
          (((Steenrod.compBNat.app X).f (n + 1)).hom
            (Finsupp.single
              (⟨Fin.succ m, simplexEquiv X (Fin.succ m).val σ⟩ : WSIndex (n + 1) X)
              (1 : GroupRingZ2)))
        + cochainEval (m.val + 1)
            (cochainCoboundary (ZMod 2) X m.val
              (homCochain Steenrod.compBNat compA_eq_compBNat_zero X p q α β n m)) σ := by
  rw [fourEval_compA_eq_compB Steenrod.compBNat compA_eq_compBNat_zero X p q α β hα hβ n
      (Fin.succ m) (simplexEquiv X (Fin.succ m).val σ),
    fourEval_s_wDiffS Steenrod.compBNat compA_eq_compBNat_zero X p q α β n m σ]

end

end GroupApproximation.CharClass
