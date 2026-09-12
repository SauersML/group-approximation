import GroupApproximation.CharClass.CartanCochainId

/-!
# The Cartan formula as an identity of cochains

The evaluated identity holds on every simplex of the degree, so it is an identity
of cochains.  The right-hand side is packaged as a cochain by naming the function
it is; nothing else changes.

## Main results

* `cartanRhsCochain` — the right-hand side, as a cochain.
* `cartan_cochain` — **the Cartan formula, as an identity of cochains**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The right-hand side of the Cartan formula, as a cochain: the sum over the
splittings of the resolution index of the cup product of the two cup-`i`
squares. -/
noncomputable def cartanRhsCochain (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (d e : ℕ) : singularCochainGroup (ZMod 2) X (d + 1) :=
  cochainOfFun (d + 1) fun σ =>
    ∑ j' ∈ Finset.range (e + 1),
      evAt X (p + p - j' + (q + q - (e - j')))
        (cochainCup (p + p - j') (q + q - (e - j'))
          (cochainCupI j' p p (p + p - j') α α)
          (cochainCupI (e - j') q q (q + q - (e - j')) β β)) (d + 1) σ

/-- **The Cartan formula, as an identity of cochains.**  The square of the cup
product is the right-hand side plus a coboundary. -/
theorem cartan_cochain (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n j d e : ℕ) (hn : n + 1 = p + q + (p + q)) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : d + 1 + e = n + 1) (hdn : d < n + 1) :
    cochainCast hd.symm (sqCochain (p + q) j (cochainCup p q α β))
      = cartanRhsCochain X p q α β d e
        + cochainCoboundary (ZMod 2) X d
            (homCochain Steenrod.compBNat compA_eq_compBNat_zero X p q α β n
              ⟨d, hdn⟩) := by
  apply cochain_ext
  intro σ
  rw [cochainEval_add, cartanRhsCochain, cochainEval_cochainOfFun]
  exact cartan_cochainEval X p q α β hα hβ n j d e hn hj hd he hdn σ

end

end GroupApproximation.CharClass
