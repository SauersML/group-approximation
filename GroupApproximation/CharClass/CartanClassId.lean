import GroupApproximation.CharClass.CartanCochainFormula
import GroupApproximation.CharClass.CartanCohomologous

/-!
# The Cartan formula, at the level of classes

The two cochains differ by a coboundary, so their classes agree.  What the class
lemmas want are the two cocycle proofs, and both come out of what is already
here: the square of a cup product of cocycles is a cocycle, a degree cast
preserves that, and the right-hand side is then a cocycle because the identity
says it is one plus a coboundary.

## Main results

* `cochainCoboundary_cochainCast` — the coboundary of a cast is the cast of the
  coboundary.
* `cartanRhs_cocycle` — the right-hand side is a cocycle.
* `cartan_class` — **the Cartan formula, as an identity of cohomology classes**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Degree casts and the coboundary -/

theorem cochainCast_zero {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    cochainCast h (0 : singularCochainGroup (ZMod 2) X m) = 0 := by
  subst h
  rw [cochainCast_rfl]

/-- **The coboundary of a cast is the cast of the coboundary.** -/
theorem cochainCoboundary_cochainCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m) :
    cochainCoboundary (ZMod 2) X m' (cochainCast h φ)
      = cochainCast (by omega : m + 1 = m' + 1) (cochainCoboundary (ZMod 2) X m φ) := by
  subst h
  rw [cochainCast_rfl]
  exact (cochainCast_rfl _).symm

theorem cochainCoboundary_cochainCast_eq_zero {X : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m)
    (hφ : cochainCoboundary (ZMod 2) X m φ = 0) :
    cochainCoboundary (ZMod 2) X m' (cochainCast h φ) = 0 := by
  rw [cochainCoboundary_cochainCast, hφ, cochainCast_zero]

/-! ## 2. The two cocycle proofs -/

variable {X : TopCat.{0}} {p q : ℕ}
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

/-- The square of the cup product, cast, is a cocycle. -/
theorem cast_sqCochain_cocycle
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (j d : ℕ) (hd : d + 1 = j + (p + q)) :
    cochainCoboundary (ZMod 2) X (d + 1)
        (cochainCast hd.symm (sqCochain (p + q) j (cochainCup p q α β))) = 0 :=
  cochainCoboundary_cochainCast_eq_zero hd.symm _
    (sqCochain_cocycle (p + q) j (cochainCup p q α β)
      (cochainCupZMod2_respects_cocycles p q α β hα hβ))

/-- **The right-hand side is a cocycle**, because the identity presents it as a
cocycle minus a coboundary. -/
theorem cartanRhs_cocycle
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n j d e : ℕ) (hn : n + 1 = p + q + (p + q)) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : d + 1 + e = n + 1) (hdn : d < n + 1) :
    cochainCoboundary (ZMod 2) X (d + 1) (cartanRhsCochain X p q α β d e) = 0 := by
  have hid := cartan_cochain X p q α β hα hβ n j d e hn hj hd he hdn
  have h0 := cast_sqCochain_cocycle α β hα hβ j d hd
  rw [hid, cochainCoboundary_add, cochainCoboundary_cochainCoboundary, add_zero] at h0
  exact h0

/-! ## 3. The Cartan formula on classes -/

/-- **The Cartan formula, as an identity of cohomology classes.** -/
theorem cartan_class
    (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (n j d e : ℕ) (hn : n + 1 = p + q + (p + q)) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : d + 1 + e = n + 1) (hdn : d < n + 1) :
    cocycleClass X (d + 1)
        (cochainCast hd.symm (sqCochain (p + q) j (cochainCup p q α β)))
        (cast_sqCochain_cocycle α β hα hβ j d hd)
      = cocycleClass X (d + 1) (cartanRhsCochain X p q α β d e)
          (cartanRhs_cocycle α β hα hβ n j d e hn hj hd he hdn) := by
  have hid := cartan_cochain X p q α β hα hβ n j d e hn hj hd he hdn
  have hsum : cochainCoboundary (ZMod 2) X (d + 1)
      (cartanRhsCochain X p q α β d e
        + cochainCoboundary (ZMod 2) X d
            (homCochain Steenrod.compBNat compA_eq_compBNat_zero X p q α β n
              ⟨d, hdn⟩)) = 0 := by
    rw [← hid]
    exact cast_sqCochain_cocycle α β hα hβ j d hd
  refine (cocycleClass_congr X (d + 1) hid
    (cast_sqCochain_cocycle α β hα hβ j d hd) hsum).trans ?_
  exact cocycleClass_add_coboundary X d _
    (cartanRhs_cocycle α β hα hβ n j d e hn hj hd he hdn) _ hsum

end

end GroupApproximation.CharClass
