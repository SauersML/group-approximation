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

theorem exists_gl_of_eHigh_module_comm (hm : PureCharPrimeEHighModuleStatement) {B Q : Type}
    [CommGroup B] [Group Q] (φ : Q →* MulAut B) (hQ : ∀ a b : Q, a * b = b * a) {p : ℕ}
    (hp : p.Prime) {e : ℕ} (he : 2 ≤ e) (hexp : ∀ b : B, b ^ (p ^ e) = 1)
    (hmin : ∃ b : B, b ^ (p ^ (e - 1)) ≠ 1) (hfg : Group.FG (B ⋊[φ] Q)) :
    ∃ (K : Type) (_ : Field K) (d : ℕ) (f : (B ⋊[φ] Q) →* GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective f := by
  haveI : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  haveI : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) (EOneMod φ (p ^ e) hexp) :=
    eOne_finite hfg
  haveI hQfg : Group.FG Q := by
    haveI := hfg
    exact Group.fg_of_surjective (SemidirectProduct.rightHom_surjective (φ := φ))
  have hwit : ∃ m : EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q,
      p ^ (e - 1) • m ≠ 0 := by
    obtain ⟨b, hb⟩ := hmin
    refine ⟨(eOneOf (φ := φ) (hV := hexp) b, 0), fun h => hb ?_⟩
    have h2 : p ^ (e - 1) • eOneOf (φ := φ) (hV := hexp) b = 0 := congrArg Prod.fst h
    have h3 : (Additive.ofMul (b ^ (p ^ (e - 1))) : Additive B) = Additive.ofMul 1 := by
      rw [ofMul_pow]
      exact h2
    exact Additive.ofMul.injective h3
  obtain ⟨K, hK, d, κ', ρ, hchar, hκ', hequiv⟩ :=
    hm p hp e he Q hQ hQfg (EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q)
      inferInstance hwit
  let κ : B →* GeneralLinearGroup (Fin d) K := κ'.comp (eHighInl φ hexp)
  have hκ : ∀ (q : Q) (b : B), κ (φ q b) = ρ q * κ b * (ρ q)⁻¹ := by
    intro q b
    have h2 : ((eOneOf (φ := φ) (hV := hexp) (φ q b), (0 : MonoidAlgebra (ZMod (p ^ e)) Q)) :
        EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) =
        MonoidAlgebra.of (ZMod (p ^ e)) Q q •
          ((eOneOf (φ := φ) (hV := hexp) b, 0) :
            EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q) :=
      Prod.ext (eOne_smul (φ := φ) (hV := hexp) q (eOneOf (φ := φ) (hV := hexp) b)).symm
        (smul_zero (MonoidAlgebra.of (ZMod (p ^ e)) Q q)).symm
    show κ' (eHighInl φ hexp (φ q b)) = ρ q * κ' (eHighInl φ hexp b) * (ρ q)⁻¹
    exact (congrArg (fun m : EOneMod φ (p ^ e) hexp × MonoidAlgebra (ZMod (p ^ e)) Q =>
      κ' (Multiplicative.ofAdd m)) h2).trans (hequiv q _)
  have hκi : Function.Injective κ := by
    intro a b hab
    have hab' : κ' (eHighInl φ hexp a) = κ' (eHighInl φ hexp b) := hab
    exact eHighInl_injective φ hexp (hκ' hab')
  have hρ : ∀ (q : Q) (b : B), ρ q = κ b → q = 1 := by
    intro q b hqb
    have h3 := hequiv q ((0 : EOneMod φ (p ^ e) hexp), (1 : MonoidAlgebra (ZMod (p ^ e)) Q))
    have hcomm : κ b * κ' (Multiplicative.ofAdd ((0 : EOneMod φ (p ^ e) hexp),
        (1 : MonoidAlgebra (ZMod (p ^ e)) Q))) =
        κ' (Multiplicative.ofAdd ((0 : EOneMod φ (p ^ e) hexp),
          (1 : MonoidAlgebra (ZMod (p ^ e)) Q))) * κ b := by
      show κ' (eHighInl φ hexp b) * _ = _ * κ' (eHighInl φ hexp b)
      rw [← map_mul, ← map_mul, mul_comm (eHighInl φ hexp b)]
    rw [hqb, hcomm, mul_inv_cancel_right] at h3
    have h4 : MonoidAlgebra.of (ZMod (p ^ e)) Q q * 1 = 1 :=
      congrArg Prod.snd (Multiplicative.ofAdd.injective (hκ' h3))
    have h5 : MonoidAlgebra.of (ZMod (p ^ e)) Q q = MonoidAlgebra.of (ZMod (p ^ e)) Q 1 := by
      rw [map_one]
      exact (mul_one _).symm.trans h4
    exact MonoidAlgebra.of_injective h5
  exact ⟨K, hK, d, eHighConjGL κ ρ hκ, hchar, eHighConjGL_injective κ ρ hκ hκi hρ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_gl_of_eHigh_module_comm

/-- **Endpoint.**  The high-exponent group statement follows from its module form. -/
theorem pureCharPrimeEHigh_of_module (hm : PureCharPrimeEHighModuleStatement) :
    PureCharPrimeEHighStatement := by
  intro B Q _ _ φ hB hQ p hp e he hexp hmin hfg
  letI : CommGroup B := { ‹Group B› with mul_comm := hB }
  exact exists_gl_of_eHigh_module_comm hm φ hQ hp he hexp hmin hfg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharPrimeEHigh_of_module

end GroupApproximation.BooneHigman.Metabelian.Coprimary
