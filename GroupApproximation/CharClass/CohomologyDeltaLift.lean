import GroupApproximation.CharClass.CohomologyMayerVietoris
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The Mayer–Vietoris connecting map, computed from a lift

Mathlib's `ShortComplex.ShortExact.δ_apply` describes the connecting map of a short
exact sequence of complexes element-wise: to compute `δ` on the class of a cocycle
`x₃`, lift `x₃` along `g` to some `x₂`, differentiate, and descend along `f` to
some `x₁`; then `δ [x₃] = [x₁]`.  Both choices are free, which is what makes the
description usable: one may lift with the splitting, or with anything else that is
convenient — in particular with something that is manifestly compatible with a cup
product.

This file specialises that description to the Mayer–Vietoris short exact sequence
`mvCoSC` of `CohomologyMayerVietoris.lean`, and records that a descended `x₁` is
automatically a cocycle.  It is the entry point for the `H^*(X)`-linearity of the
connecting map, `δ (a ⌣ b|_{U ⊓ V}) = δ a ⌣ b`.

## Main declarations

* `MVDelta.cls₃`, `MVDelta.cls₁` — the classes of cocycles of the outer terms.
* `MVDelta.d_eq_zero_of_descends` — a descended element is a cocycle.
* `MVDelta.delta_apply` — `δ [x₃] = [x₁]` for any lift and any descent.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-- The class in `H^p(X₃)` of a cocycle of the third term. -/
def cls₃ (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) (x₃ : (mvCoSC U V hUV).X₃.X p)
    (hx₃ : ((mvCoSC U V hUV).X₃.d p (p + 1)).hom x₃ = 0) :
    (mvCoSC U V hUV).X₃.homology p :=
  ((mvCoSC U V hUV).X₃.homologyπ p).hom
    ((mvCoSC U V hUV).X₃.cyclesMk x₃ (p + 1) (ComplexShape.next_eq' _ (upRel p)) hx₃)

/-- The class in `H^{p+1}(X₁)` of a cocycle of the first term. -/
def cls₁ (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) (x₁ : (mvCoSC U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSC U V hUV).X₁.d (p + 1) (p + 2)).hom x₁ = 0) :
    (mvCoSC U V hUV).X₁.homology (p + 1) :=
  ((mvCoSC U V hUV).X₁.homologyπ (p + 1)).hom
    ((mvCoSC U V hUV).X₁.cyclesMk x₁ (p + 2) (ComplexShape.next_eq' _ (upRel (p + 1))) hx₁)

/-- **A descended element is a cocycle.**  If `f x₁ = d x₂` then `d x₁ = 0`,
because `f` is a monomorphism and `d ∘ d = 0`. -/
theorem d_eq_zero_of_descends (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (x₂ : (mvCoSC U V hUV).X₂.X p) (x₁ : (mvCoSC U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSC U V hUV).f.f (p + 1)).hom x₁
      = ((mvCoSC U V hUV).X₂.d p (p + 1)).hom x₂) :
    ((mvCoSC U V hUV).X₁.d (p + 1) (p + 2)).hom x₁ = 0 :=
  (mvCoSC_shortExact U V hUV).d_eq_zero_of_f_eq_d_apply p (p + 1) x₂ x₁ hx₁ (p + 2)

/-- **The connecting map from a lift.**  Lift the cocycle `x₃` along `g` to `x₂`,
differentiate, descend along `f` to `x₁`; then `δ` takes the class of `x₃` to the
class of `x₁`.  Both `x₂` and `x₁` are arbitrary subject to their equations. -/
theorem delta_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (x₃ : (mvCoSC U V hUV).X₃.X p)
    (hx₃ : ((mvCoSC U V hUV).X₃.d p (p + 1)).hom x₃ = 0)
    (x₂ : (mvCoSC U V hUV).X₂.X p)
    (hx₂ : ((mvCoSC U V hUV).g.f p).hom x₂ = x₃)
    (x₁ : (mvCoSC U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSC U V hUV).f.f (p + 1)).hom x₁
      = ((mvCoSC U V hUV).X₂.d p (p + 1)).hom x₂) :
    ((mvCoSC_shortExact U V hUV).δ p (p + 1) (upRel p)).hom (cls₃ U V hUV p x₃ hx₃)
      = cls₁ U V hUV p x₁ (d_eq_zero_of_descends U V hUV p x₂ x₁ hx₁) :=
  (mvCoSC_shortExact U V hUV).δ_apply p (p + 1) (upRel p) x₃ hx₃ x₂ hx₂ x₁ hx₁ (p + 2)
    (ComplexShape.next_eq' _ (upRel (p + 1)))

end MVDelta

end

end GroupApproximation.CharClass
