import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.ZMod.Basic
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEStatement
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEAffine
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOneModule
import GroupApproximation.Meta.AxiomGuard

/-!
# Exponent `p`: linearity of a f.g. split extension from the module statement (bh-met-26)

Assume `PureCharPrimeEOneStatement`.  Let `B` be abelian with `b ^ p = 1`, `Q` abelian and
`B ⋊[φ] Q` finitely generated.  Then `M = EOneMod φ p hexp × F_p[Q]` is a finite
`F_p[Q]`-module (`eOne_finite` plus the regular summand).  The statement gives an additive
embedding `ι : M ↪ K^d` intertwining `Q` with `ρ : Q →* GL_d(K)`.

* `κ b := ι (b, 0)` is additive, injective and satisfies `κ (φ q b) = ρ q *ᵥ κ b`.
* `ρ` is injective, because `ι (q • (0, 1)) = ι (0, q)` and `MonoidAlgebra.of` is injective.
  This is the reason for the regular summand.
* The affine representation `eAffineGL` is injective into `GL_{d+1}(K)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

theorem exists_gl_of_exponent_prime_comm (h1 : PureCharPrimeEOneStatement) {B Q : Type}
    [CommGroup B] [Group Q] (φ : Q →* MulAut B) (hQ : ∀ a b : Q, a * b = b * a) {p : ℕ}
    (hp : p.Prime) (hexp : ∀ b : B, b ^ p = 1) (hfg : Group.FG (B ⋊[φ] Q)) :
    ∃ (K : Type) (_ : Field K) (d : ℕ) (f : (B ⋊[φ] Q) →* GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective f := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  haveI : Module.Finite (MonoidAlgebra (ZMod p) Q) (EOneMod φ p hexp) := eOne_finite hfg
  haveI hQfg : Group.FG Q := by
    haveI := hfg
    exact Group.fg_of_surjective (SemidirectProduct.rightHom_surjective (φ := φ))
  obtain ⟨K, hK, d, ι, ρ, hchar, hι, hequiv⟩ :=
    h1 p hp Q hQ hQfg (EOneMod φ p hexp × MonoidAlgebra (ZMod p) Q) inferInstance
  let κ : B → (Fin d → K) := fun b => ι (eOneOf (φ := φ) (hV := hexp) b, 0)
  have hzero : κ 1 = 0 := map_zero ι
  have hadd : ∀ a b : B, κ (a * b) = κ a + κ b := by
    intro a b
    show ι (eOneOf (φ := φ) (hV := hexp) (a * b), 0) =
      ι (eOneOf (φ := φ) (hV := hexp) a, 0) + ι (eOneOf (φ := φ) (hV := hexp) b, 0)
    have h2 : ((eOneOf (φ := φ) (hV := hexp) (a * b), (0 : MonoidAlgebra (ZMod p) Q)) :
        EOneMod φ p hexp × MonoidAlgebra (ZMod p) Q) =
        (eOneOf (φ := φ) (hV := hexp) a, 0) + (eOneOf (φ := φ) (hV := hexp) b, 0) :=
      Prod.ext rfl (add_zero (0 : MonoidAlgebra (ZMod p) Q)).symm
    exact (congrArg ι h2).trans (map_add ι _ _)
  have hκ : ∀ (q : Q) (b : B), κ (φ q b) = (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ κ b := by
    intro q b
    show ι (eOneOf (φ := φ) (hV := hexp) (φ q b), 0) =
      (ρ q : Matrix (Fin d) (Fin d) K) *ᵥ ι (eOneOf (φ := φ) (hV := hexp) b, 0)
    have h2 : ((eOneOf (φ := φ) (hV := hexp) (φ q b), (0 : MonoidAlgebra (ZMod p) Q)) :
        EOneMod φ p hexp × MonoidAlgebra (ZMod p) Q) =
        MonoidAlgebra.of (ZMod p) Q q •
          ((eOneOf (φ := φ) (hV := hexp) b, 0) : EOneMod φ p hexp × MonoidAlgebra (ZMod p) Q) :=
      Prod.ext (eOne_smul (φ := φ) (hV := hexp) q (eOneOf (φ := φ) (hV := hexp) b)).symm
        (smul_zero (MonoidAlgebra.of (ZMod p) Q q)).symm
    exact (congrArg ι h2).trans (hequiv q _)
  have hκi : Function.Injective κ := by
    intro a b hab
    have h2 : (eOneOf (φ := φ) (hV := hexp) a, (0 : MonoidAlgebra (ZMod p) Q)) =
        (eOneOf (φ := φ) (hV := hexp) b, 0) := hι hab
    exact Additive.ofMul.injective (congrArg Prod.fst h2)
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h3 := hequiv q ((0 : EOneMod φ p hexp), (1 : MonoidAlgebra (ZMod p) Q))
    rw [hq, Units.val_one, Matrix.one_mulVec] at h3
    have h4 : MonoidAlgebra.of (ZMod p) Q q * 1 = 1 := congrArg Prod.snd (hι h3)
    have h5 : MonoidAlgebra.of (ZMod p) Q q = MonoidAlgebra.of (ZMod p) Q 1 := by
      rw [map_one]
      exact (mul_one _).symm.trans h4
    exact MonoidAlgebra.of_injective h5
  exact ⟨K, hK, d + 1, eAffineGL κ ρ hzero hadd hκ, hchar,
    eAffineGL_injective κ ρ hzero hadd hκ hκi hρi⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_gl_of_exponent_prime_comm

theorem exists_gl_of_exponent_prime (h1 : PureCharPrimeEOneStatement) {B Q : Type}
    [Group B] [Group Q] (φ : Q →* MulAut B) (hB : ∀ a b : B, a * b = b * a)
    (hQ : ∀ a b : Q, a * b = b * a) {p : ℕ} (hp : p.Prime) (hexp : ∀ b : B, b ^ p = 1)
    (hfg : Group.FG (B ⋊[φ] Q)) :
    ∃ (K : Type) (_ : Field K) (d : ℕ) (f : (B ⋊[φ] Q) →* GeneralLinearGroup (Fin d) K),
      ringChar K = p ∧ Function.Injective f := by
  letI : CommGroup B := { ‹Group B› with mul_comm := hB }
  exact exists_gl_of_exponent_prime_comm h1 φ hQ hp hexp hfg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_gl_of_exponent_prime

end GroupApproximation.BooneHigman.Metabelian.Coprimary
