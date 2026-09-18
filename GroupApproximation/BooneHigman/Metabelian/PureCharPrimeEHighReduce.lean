import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.ZMod.Basic
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEStatement
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneModule
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighModule
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighConj
import GroupApproximation.Meta.AxiomGuard

/-!
# High exponent: linearity of a f.g. split extension from the module statement (bh-met-56b)

Endpoint: `pureCharPrimeEHigh_of_module :
  PureCharPrimeEHighModuleStatement → PureCharPrimeEHighStatement`.

Route.  Let `B` be abelian with `b ^ p ^ e = 1`, some `b ^ p ^ (e - 1) ≠ 1`, `e ≥ 2`, `Q` abelian
and `B ⋊[φ] Q` finitely generated.  Put `R = (ℤ/p^e)[Q]` and `M = EOneMod φ (p ^ e) hexp × R`.
`M` is a finite `R`-module (`eOne_finite` plus the regular summand) and `p ^ (e - 1) • (b, 0) ≠ 0`.
The module statement gives an injective `κ' : Multiplicative M →* GL_d(K)` and
`ρ : Q →* GL_d(K)` with `κ' (q • m) = ρ q * κ' m * (ρ q)⁻¹`.

* `κ = κ' ∘ eHighInl`, where `eHighInl b = (b, 0)`, is injective and intertwines `φ` with
  conjugation by `ρ`.
* If `ρ q = κ b`, then `ρ q` commutes with `κ' (0, 1)`, because the image of `κ'` is commutative.
  So `κ' (0, of q) = κ' (0, 1)`, hence `of q = 1` and `q = 1`.  This is why the regular summand
  is there.
* `eHighConjGL κ ρ hκ` (`PureCharPrimeEHighConj`) is then injective.

**Loud remark on strength.**  `PureCharPrimeEHighModuleStatement` is *logically equivalent* to
`PureCharPrimeEHighStatement`: the converse is routine (apply the group statement to `M ⋊ Q`).
It is strictly smaller in *proof content* only, since all group theory is removed.  Both are true
(Wehrfritz; see the docstring of `PureCharPrimeEHighModule` for an independent sketch).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

section Inl

variable {B Q : Type} [CommGroup B] [Group Q] {p e : ℕ}

/-- `b ↦ (b, 0)`, as a hom `B →* Multiplicative (EOneMod × (ℤ/p^e)[Q])`. -/
def eHighInl (φ : Q →* MulAut B) (hexp : ∀ b : B, b ^ (p ^ e) = 1) :
    B →* Multiplicative (EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) where
  toFun b := Multiplicative.ofAdd
    (eOneOf (φ := φ) (hV := hexp) b, (0 : MonoidAlgebra (ZMod (p ^ e)) Q))
  map_one' := rfl
  map_mul' a b := by
    have h2 : ((eOneOf (φ := φ) (hV := hexp) (a * b), (0 : MonoidAlgebra (ZMod (p ^ e)) Q)) :
        EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) =
        (eOneOf (φ := φ) (hV := hexp) a, 0) + (eOneOf (φ := φ) (hV := hexp) b, 0) :=
      Prod.ext rfl (add_zero (0 : MonoidAlgebra (ZMod (p ^ e)) Q)).symm
    exact congrArg Multiplicative.ofAdd h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighInl

theorem eHighInl_injective (φ : Q →* MulAut B) (hexp : ∀ b : B, b ^ (p ^ e) = 1) :
    Function.Injective (eHighInl φ hexp) := by
  intro a b hab
  have hab' : Multiplicative.ofAdd ((eOneOf (φ := φ) (hV := hexp) a,
      (0 : MonoidAlgebra (ZMod (p ^ e)) Q)) :
        EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) =
      Multiplicative.ofAdd ((eOneOf (φ := φ) (hV := hexp) b,
        (0 : MonoidAlgebra (ZMod (p ^ e)) Q)) :
          EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) :=
    hab
  have h2 : (Additive.ofMul a : Additive B) = Additive.ofMul b :=
    congrArg Prod.fst (Multiplicative.ofAdd.injective hab')
  exact Additive.ofMul.injective h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighInl_injective

end Inl

