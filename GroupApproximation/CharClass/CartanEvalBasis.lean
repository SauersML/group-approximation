import GroupApproximation.CharClass.CartanEvalSquare
import GroupApproximation.CharClass.CartanSourceBoundary

/-!
# Composite A on a basis element of the source

The master identity is stated on a basis element `e_i ⊗ σ` of `W ⊗ S(X)`, where
the simplex is a map out of the standard simplex; composite A's evaluation is
stated on Steenrod's diagonal, where the simplex is a singular simplex.  The two
differ by the identification `simplexEquiv`, which is the identity up to a
universe lift, and this file crosses it once.

## Main results

* `compA_single` — composite A on a basis element.
* `fourEval_compA_single` — **composite A evaluated on a basis element** is the
  cochain representing the square of the cup product.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- Composite A on a basis element of the source is `Φ₀ ⊗ Φ₀` applied to
Steenrod's diagonal. -/
theorem compA_single (X : TopCat.{0}) (k : ℕ) (i : Fin (k + 1))
    (τ : singularSimplices X i.val) :
    ((compA.app X).f k).hom
        (Finsupp.single (⟨i, simplexEquiv X i.val τ⟩ : WSIndex k X) (1 : GroupRingZ2))
      = tenHom (awHom X) (awHom X) k (Steenrod.phiPair X k ⟨i, τ⟩) := by
  show awTenLambda X k
      (Steenrod.PhiHom X k
        (Finsupp.single (⟨i, simplexEquiv X i.val τ⟩ : WSIndex k X) (1 : GroupRingZ2))) = _
  rw [Steenrod.PhiHom_single, one_smul,
    show Steenrod.wsOfHom X k
        (⟨i, simplexEquiv X i.val τ⟩ : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X)
          = ⟨i, τ⟩ from by
      show (⟨i, (simplexEquiv X i.val).symm (simplexEquiv X i.val τ)⟩ :
        Steenrod.WSIndex X k) = _
      rw [Equiv.symm_apply_apply]]
  rfl

/-- **Composite A evaluated on a basis element of the source** is the cochain
whose class is the `j`-th square of the cup product. -/
theorem fourEval_compA_single (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (j : ℕ) (hj : j ≤ p + q) (σ : singularSimplices X (j + (p + q))) :
    fourEvalF2 X p q α β (p + q + (p + q))
        (((compA.app X).f (p + q + (p + q))).hom
          (Finsupp.single
            (⟨⟨j + (p + q), by omega⟩, simplexEquiv X (j + (p + q)) σ⟩ :
              WSIndex (p + q + (p + q)) X) (1 : GroupRingZ2)))
      = cochainEval (j + (p + q)) (sqCochain (p + q) j (cochainCup p q α β)) σ := by
  rw [compA_single X (p + q + (p + q)) ⟨j + (p + q), by omega⟩ σ,
    fourEvalF2_compA_sqCochain p q α β j hj σ]

end

end GroupApproximation.CharClass
