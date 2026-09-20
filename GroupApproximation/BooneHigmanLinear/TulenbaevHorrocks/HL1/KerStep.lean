import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.KerSurj
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.Dilation

/-!
# The kernel step of Tulenbaev's Cor 4.2 (k2-poly H.L1)

Let `A` be local with residue field `k`, `B = A[T⁻¹] + 𝔪[T]` and `R = A[T, T⁻¹]`. Reducing
coefficients mod `𝔪` sends `B` onto `k[T⁻¹]`: this is `ρ : B →+* k[X]`, with `X ↦ T⁻¹` giving back
the reduction (`toLaurentNeg_rho`). Its kernel is `𝔪R ∩ B` (`ker_rho_le`).

`kerStepAt`: if `St_N(k[X]) → St_N(k[T, T⁻¹])`, `X ↦ T⁻¹`, is injective (the field case, part of
`StHorrocksAt k N`), then every `α ∈ St_N(B)` that dies in `St_N(R)` dies in `St_N(k[X])`, so it lies
in the image of Tulenbaev's relative group `St_N(B, 𝔪R ∩ B)` (`KerSurj.ker_ringMap_le_range_can`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open LaurentPolynomial
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found
open GroupApproximation.BooneHigmanLinear.Tulenbaev (toLaurentNeg)

variable (A : Type) [CommRing A] [IsLocalRing A]

/-- Reduction of coefficients, `A[T, T⁻¹] → k[T, T⁻¹]`. -/
noncomputable abbrev resL : LaurentPolynomial A →+* LaurentPolynomial (IsLocalRing.ResidueField A) :=
  AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue A)

variable {A}

theorem resL_single (n : ℤ) (c : A) :
    resL A (AddMonoidAlgebra.single n c) = AddMonoidAlgebra.single n (IsLocalRing.residue A c) := by
  refine LaurentPolynomial.ext fun m => ?_
  rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem toLaurentNeg_injective (k : Type) [CommRing k] : Function.Injective (toLaurentNeg k) := by
  intro p q h
  rw [toLaurentNeg_apply, toLaurentNeg_apply] at h
  exact Polynomial.toLaurent_injective (LaurentPolynomial.invert.injective h)

variable (A)

/-- `resL ∘ (X ↦ T⁻¹) = (X ↦ T⁻¹) ∘ (reduction of coefficients)`. -/
theorem resL_comp_toLaurentNeg :
    (resL A).comp (toLaurentNeg A) =
      (toLaurentNeg (IsLocalRing.ResidueField A)).comp
        (Polynomial.mapRingHom (IsLocalRing.residue A)) := by
  apply Polynomial.ringHom_ext
  · intro a
    have e1 := RingHom.congr_fun (toLaurentNeg_comp_C (A := A)) a
    have e2 := RingHom.congr_fun (toLaurentNeg_comp_C (A := IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a)
    rw [RingHom.comp_apply] at e1 e2
    rw [RingHom.comp_apply, RingHom.comp_apply, e1, Polynomial.coe_mapRingHom, Polynomial.map_C, e2,
      ← single_eq_C, ← single_eq_C, resL_single]
  · rw [RingHom.comp_apply, RingHom.comp_apply, toLaurentNeg_X, Polynomial.coe_mapRingHom,
      Polynomial.map_X, toLaurentNeg_X, T, T, resL_single, map_one]

theorem toLaurentNeg_C_mul_X_pow (c : A) (m : ℕ) :
    toLaurentNeg A (Polynomial.C c * Polynomial.X ^ m) = AddMonoidAlgebra.single (-(m : ℤ)) c := by
  have e := RingHom.congr_fun (toLaurentNeg_comp_C (A := A)) c
  rw [RingHom.comp_apply] at e
  rw [map_mul, map_pow, e, toLaurentNeg_X, T_pow, single_eq_C_mul_T,
    show ((m : ℕ) : ℤ) * -1 = -(m : ℤ) by ring]

/-- The reduction of an element of `B` lies in `k[T⁻¹]`. -/
theorem resL_mem_range {f : LaurentPolynomial A} (hf : f ∈ horrBm A) :
    resL A f ∈ (toLaurentNeg (IsLocalRing.ResidueField A)).range := by
  induction hf using Graded.horrB_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg ihf ihg => rw [map_add]; exact add_mem ihf ihg
  | monomial n c hc =>
    by_cases hn : n ≤ 0
    · refine RingHom.mem_range.2 ⟨Polynomial.map (IsLocalRing.residue A) (Polynomial.C c * Polynomial.X ^ (-n).toNat), ?_⟩
      have e := RingHom.congr_fun (resL_comp_toLaurentNeg A)
        (Polynomial.C c * Polynomial.X ^ (-n).toNat)
      rw [RingHom.comp_apply, RingHom.comp_apply, toLaurentNeg_C_mul_X_pow,
        show -(((-n).toNat : ℕ) : ℤ) = n by omega, Polynomial.coe_mapRingHom] at e
      exact e.symm
    · have hc' : c ∈ IsLocalRing.maximalIdeal A := hc (by omega)
      rw [resL_single, (IsLocalRing.residue_eq_zero_iff c).2 hc', AddMonoidAlgebra.single_zero]
      exact zero_mem _

variable {A}

/-- `(X ↦ T⁻¹)` as an isomorphism onto its image, for the residue field. -/
noncomputable def negEquiv (k : Type) [CommRing k] : Polynomial k ≃+* (toLaurentNeg k).range :=
  RingEquiv.ofBijective (toLaurentNeg k).rangeRestrict
    ⟨fun p q h => toLaurentNeg_injective k (congrArg Subtype.val h),
      (toLaurentNeg k).rangeRestrict_surjective⟩

variable (A)

/-- **`ρ : B →+* k[X]`**: reduce the coefficients mod `𝔪` and read `T⁻¹` as `X`. -/
noncomputable def rho : horrBm A →+* Polynomial (IsLocalRing.ResidueField A) :=
  (negEquiv (IsLocalRing.ResidueField A)).symm.toRingHom.comp
    (((resL A).comp (horrBm A).subtype).codRestrict _ fun f => resL_mem_range A f.2)

theorem toLaurentNeg_rho (f : horrBm A) :
    toLaurentNeg (IsLocalRing.ResidueField A) (rho A f) = resL A f := by
  have h := congrArg Subtype.val ((negEquiv (IsLocalRing.ResidueField A)).apply_symm_apply
    (((resL A).comp (horrBm A).subtype).codRestrict _ fun f => resL_mem_range A f.2) f)
  exact h

theorem toLaurentNeg_comp_rho :
    (toLaurentNeg (IsLocalRing.ResidueField A)).comp (rho A) = (resL A).comp (horrBm A).subtype :=
  RingHom.ext fun f => toLaurentNeg_rho A f

theorem rho_surjective : Function.Surjective (rho A) := by
  intro q
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue A)
    IsLocalRing.residue_surjective q
  refine ⟨negB (IsLocalRing.maximalIdeal A) q', toLaurentNeg_injective _ ?_⟩
  rw [toLaurentNeg_rho]
  have e := RingHom.congr_fun (resL_comp_toLaurentNeg A) q'
  rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom] at e
  exact e

theorem ker_rho_le : RingHom.ker (rho A) ≤ mB A := by
  intro f hf
  rw [RingHom.mem_ker] at hf
  have h := toLaurentNeg_rho A f
  rw [hf, map_zero] at h
  show ((f : LaurentPolynomial A)) ∈ coeffIdeal (IsLocalRing.maximalIdeal A)
  rw [coeffIdeal, RingHom.mem_ker]
  exact h.symm

/-- **The kernel step.** From the field case at the residue field. -/
theorem kerStepAt {N : ℕ} (hk : Function.Injective
      (ringMap (I := Fin N) (toLaurentNeg (IsLocalRing.ResidueField A))))
    (hB : VdK.Elements (Fin N) (horrBm A)) : KerStepAt A N hB := by
  intro α hα
  have h1 : ringMap (I := Fin N) (toLaurentNeg (IsLocalRing.ResidueField A)) (ringMap (rho A) α) =
      ringMap (toLaurentNeg (IsLocalRing.ResidueField A)) 1 := by
    rw [ringMap_ringMap, toLaurentNeg_comp_rho, ← ringMap_ringMap, hα, map_one, map_one]
  have h2 : α ∈ (ringMap (I := Fin N) (rho A)).ker := MonoidHom.mem_ker.2 (hk h1)
  exact ker_ringMap_le_range_can hB (rho A) (rho_surjective A) (ker_rho_le A) h2

#audit_axioms kerStepAt

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
