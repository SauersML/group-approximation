import GroupApproximation.CharClass.SteenrodPairBoundary

/-!
# Pairing the diagonal against two cochains

The cup-`i` product and the cut diagonal are the same object seen from two
sides: both are a sum over the `(i+1)`-element cut sets of an `n`-simplex, one
recording the *product of the values* of two cochains on the two alternating
faces, the other recording the *pair of faces* itself.  So evaluating the cup-`i`
product on a simplex is the same as pairing the two cochains against the
diagonal.

This file is that identity.  It is what lets the evaluated Cartan comparison,
which lives on the chain side in the fourfold, be read back as a statement about
the squares, which live on the cochain side.

## Main results

* `pairEval` — the pairing of a bidegree of `S(X) ⊗ S(X)` against two cochains.
* `pairEval_facePair` — on one cut, the pairing is the product of two
  `faceVal`s; both sides vanish off the correct bidegree, for the same reason.
* `pairEval_steenrodDiag` — **the bridge**: the pairing against the diagonal is
  the evaluation of the cup-`i` product.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-- **Pairing a bidegree of the tensor square against two cochains**: on a basis
pair, the product of the two values, extended linearly. -/
noncomputable def pairEval (a b : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b) :
    tensorTwo X a b →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2)
    (fun p : singularSimplices X a × singularSimplices X b =>
      cochainEval a α p.1 * cochainEval b β p.2)

theorem pairEval_single (a b : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b)
    (p : singularSimplices X a × singularSimplices X b) (c : ZMod 2) :
    pairEval a b α β (Finsupp.single p c)
      = c * (cochainEval a α p.1 * cochainEval b β p.2) := by
  unfold pairEval
  simp

/-- On a single cut, the pairing is the product of the two face values.  Both
sides vanish when either family has the wrong size, and for the same reason. -/
theorem pairEval_facePair (a b : ℕ) {n : ℕ}
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b)
    (σ : singularSimplices X n) (A B : Finset (Fin (n + 1))) :
    pairEval a b α β (facePair a b σ A B) = faceVal a α σ A * faceVal b β σ B := by
  by_cases hA : A.card = a + 1
  · by_cases hB : B.card = b + 1
    · rw [facePair_of_card a b σ hA hB, pairEval_single, faceVal_of_card a α σ hA,
        faceVal_of_card b β σ hB, one_mul]
    · rw [facePair_eq_zero_right a b σ hB, map_zero, faceVal_of_card_ne β σ hB,
        mul_zero]
  · rw [facePair_eq_zero_left a b σ hA, map_zero, faceVal_of_card_ne α σ hA,
      zero_mul]

/-- **The bridge.**  Pairing two cochains against the cut diagonal is evaluating
their cup-`i` product.  Both sides are literally the same sum over the same cut
sets. -/
theorem pairEval_steenrodDiag (i a b n : ℕ)
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b)
    (σ : singularSimplices X n) :
    pairEval a b α β (steenrodDiag i a b σ)
      = cochainEval n (cochainCupI i a b n α β) σ := by
  unfold steenrodDiag
  rw [map_sum, cochainCupI_eval]
  exact Finset.sum_congr rfl fun S _ =>
    pairEval_facePair a b α β σ (cutU S) (cutV S)

end

end Steenrod
end CharClass
end GroupApproximation
