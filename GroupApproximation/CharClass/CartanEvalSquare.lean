import GroupApproximation.CharClass.CartanEvalComposeA
import GroupApproximation.CharClass.SteenrodSquare

/-!
# Composite A evaluates to the square of the cup product

`sqCochain m j φ` is `φ ⌣_{m-j} φ` in degree `j + m`, the cochain whose class is
`Sqʲ [φ]`.  Composite A, paired against `α, β, α, β`, is exactly that cochain for
`φ = α ⌣ β`.

The degrees line up on their own.  Composite A in total degree `m + m` on a
simplex of degree `j + m` has cup index `(m + m) - (j + m)`, which is `m - j`;
that is the cup index `sqCochain` uses, and the output degree `j + m` is the same
on both sides, so no transport appears.

## Main results

* `fourEvalF2_compA_sqCochain` — **the left-hand side of the Cartan formula**,
  at cochain level.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}} (p q : ℕ)
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

/-- **The left-hand side of the Cartan formula.**  Composite A, evaluated on the
`W`-index `j` of a simplex of degree `j + m`, is the cochain representing
`Sqʲ` of the cup product. -/
theorem fourEvalF2_compA_sqCochain (j : ℕ) (hj : j ≤ p + q)
    (σ : singularSimplices X (j + (p + q))) :
    fourEvalF2 X p q α β (p + q + (p + q))
        (tenHom (awHom X) (awHom X) (p + q + (p + q))
          (Steenrod.phiPair X (p + q + (p + q)) ⟨⟨j + (p + q), by omega⟩, σ⟩))
      = cochainEval (j + (p + q)) (sqCochain (p + q) j (cochainCup p q α β)) σ := by
  rw [fourEvalF2_compA_phiPair p q α β (p + q + (p + q)) rfl]
  show cochainEval (j + (p + q))
      (cochainCupI (p + q + (p + q) - (j + (p + q))) (p + q) (p + q) (j + (p + q))
        (cochainCup p q α β) (cochainCup p q α β)) σ = _
  rw [show p + q + (p + q) - (j + (p + q)) = p + q - j from by omega]
  rfl

end

end GroupApproximation.CharClass
