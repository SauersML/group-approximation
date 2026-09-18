import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittETrunc
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The injective ring map `D_e → W_e(L)` (bh-met-87h, part 7)

Let `L = Frac(𝔽_p[σ])` (`eHighWittE_L`) and `W_e(L) = TruncatedWittVector p e L`.

* `W_e(L)` has `p ^ e = 0`, so `ℤ → W_e(L)` factors through `ZMod (p ^ e)` (`eHighWittE_f0`).
* Let `g : ZMod (p ^ e)[σ] → W_e(L)` send `X s` to the Teichmüller lift of `X s`
  (`eHighWittE_g`).
* The zeroth coordinate of `g` is `algebraMap ∘ red` (`eHighWittE_g_c0`). So `g` sends `S` to
  units, since a truncated Witt vector over a field with nonzero zeroth coordinate is a unit.
* This gives the lift `φ : D_e →+* W_e(L)` (`eHighWittE_phi`).
* `φ` is injective (`eHighWittE_phi_injective`). Every nonzero `z ∈ D_e` is `p ^ j u` with
  `j < e` and `u` a unit (`eHighWittE_val`). Then `φ z = p ^ j φ(u) ≠ 0`, because
  `p ^ j ≠ 0` in `W_e(L)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable (p e : ℕ) [NeZero e] (σ : Type)

/-- The field `L = Frac(𝔽_p[σ])`. -/
abbrev eHighWittE_L : Type := FractionRing (MvPolynomial σ (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_L

variable [Fact p.Prime]

/-- The structure map `ZMod (p ^ e) →+* W_e(L)`. -/
def eHighWittE_f0 : ZMod (p ^ e) →+* TruncatedWittVector p e (eHighWittE_L p σ) :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ e : ℕ) : ℤ)}) (Int.castRingHom _) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_natCast, Nat.cast_pow, eHighWittE_tw_p_pow_eq_zero, mul_zero]).comp
    (Int.quotientSpanNatEquivZMod (p ^ e)).symm.toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_f0

/-- The images of the variables: Teichmüller lifts of `X s`. -/
def eHighWittE_gX (s : σ) : TruncatedWittVector p e (eHighWittE_L p σ) :=
  WittVector.truncate e (WittVector.teichmuller p
    (algebraMap (MvPolynomial σ (ZMod p)) (eHighWittE_L p σ) (MvPolynomial.X s)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_gX

/-- The ring map `g : ZMod (p ^ e)[σ] →+* W_e(L)`. -/
def eHighWittE_g : MvPolynomial σ (ZMod (p ^ e)) →+* TruncatedWittVector p e (eHighWittE_L p σ) :=
  MvPolynomial.eval₂Hom (eHighWittE_f0 p e σ) (eHighWittE_gX p e σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_g

/-- The zeroth coordinate, as a ring map `W_e(L) →+* L`. -/
def eHighWittE_c0 : TruncatedWittVector p e (eHighWittE_L p σ) →+* eHighWittE_L p σ where
  toFun x := x.coeff ⟨0, Nat.pos_of_ne_zero (NeZero.ne e)⟩
  map_one' := by
    rw [← map_one (WittVector.truncate (p := p) (R := eHighWittE_L p σ) e),
      WittVector.coeff_truncate]
    exact WittVector.one_coeff_zero _
  map_mul' x y := by
    rw [eHighWittE_tw_mul_coeff, ← TruncatedWittVector.coeff_out x,
      ← TruncatedWittVector.coeff_out y]
    exact WittVector.mul_coeff_zero _ _
  map_zero' := TruncatedWittVector.coeff_zero p e _ _
  map_add' x y := by
    rw [eHighWittE_tw_add_coeff, ← TruncatedWittVector.coeff_out x,
      ← TruncatedWittVector.coeff_out y]
    exact WittVector.add_coeff_zero _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_c0

theorem eHighWittE_c0_apply (x : TruncatedWittVector p e (eHighWittE_L p σ)) :
    eHighWittE_c0 p e σ x = x.coeff ⟨0, Nat.pos_of_ne_zero (NeZero.ne e)⟩ := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_c0_apply

/-- The zeroth coordinate of `g` is `algebraMap ∘ red`, as ring maps. -/
theorem eHighWittE_g_c0_hom :
    (eHighWittE_c0 p e σ).comp (eHighWittE_g p e σ) =
      (algebraMap (MvPolynomial σ (ZMod p)) (eHighWittE_L p σ)).comp (eHighWittE_red p e σ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_zmod
      (((eHighWittE_c0 p e σ).comp (eHighWittE_g p e σ)).comp MvPolynomial.C)
      (((algebraMap (MvPolynomial σ (ZMod p)) (eHighWittE_L p σ)).comp
        (eHighWittE_red p e σ)).comp MvPolynomial.C)) r
  · show eHighWittE_c0 p e σ (MvPolynomial.eval₂Hom (eHighWittE_f0 p e σ) (eHighWittE_gX p e σ)
        (MvPolynomial.X i)) =
      algebraMap (MvPolynomial σ (ZMod p)) (eHighWittE_L p σ) (eHighWittE_red p e σ
        (MvPolynomial.X i))
    rw [MvPolynomial.eval₂Hom_X', eHighWittE_red, MvPolynomial.map_X, eHighWittE_c0_apply,
      eHighWittE_gX, WittVector.coeff_truncate]
    exact WittVector.teichmuller_coeff_zero p _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_g_c0_hom

theorem eHighWittE_g_c0 (a : MvPolynomial σ (ZMod (p ^ e))) :
    eHighWittE_c0 p e σ (eHighWittE_g p e σ a) =
      algebraMap (MvPolynomial σ (ZMod p)) (eHighWittE_L p σ) (eHighWittE_red p e σ a) :=
  RingHom.congr_fun (eHighWittE_g_c0_hom p e σ) a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_g_c0

/-- A truncated Witt vector over `L` with nonzero zeroth coordinate is a unit. -/
theorem eHighWittE_isUnit_of_c0 (x : TruncatedWittVector p e (eHighWittE_L p σ))
    (hx : eHighWittE_c0 p e σ x ≠ 0) : IsUnit x := by
  rw [eHighWittE_c0_apply, ← TruncatedWittVector.coeff_out] at hx
  have h := (WittVector.isUnit_of_coeff_zero_ne_zero x.out hx).map (WittVector.truncate e)
  rwa [eHighWittE_truncate_out] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isUnit_of_c0

/-- `g` sends `S` to units. -/
theorem eHighWittE_g_isUnit (s : eHighWittE_S p e σ) : IsUnit (eHighWittE_g p e σ s) := by
  refine eHighWittE_isUnit_of_c0 p e σ _ ?_
  rw [eHighWittE_g_c0]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (R := MvPolynomial σ (ZMod p))
    (K := eHighWittE_L p σ) s.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_g_isUnit

/-- **The ring map `φ : D_e →+* W_e(L)`.** -/
def eHighWittE_phi : eHighWittE_D p e σ →+* TruncatedWittVector p e (eHighWittE_L p σ) :=
  IsLocalization.lift (M := eHighWittE_S p e σ) (S := eHighWittE_D p e σ)
    (eHighWittE_g_isUnit p e σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_phi

/-- **`φ` is injective.** -/
theorem eHighWittE_phi_injective : Function.Injective (eHighWittE_phi p e σ) := by
  refine (injective_iff_map_eq_zero (eHighWittE_phi p e σ)).mpr fun z hz => ?_
  by_contra hne
  obtain ⟨j, hj, u, rfl⟩ := eHighWittE_val (eHighWittE_isChain p e σ) hne
  rw [map_mul, map_pow, map_natCast] at hz
  exact eHighWittE_tw_p_pow_ne_zero hj
    ((u.isUnit.map (eHighWittE_phi p e σ)).mul_left_eq_zero.mp hz)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_phi_injective

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
