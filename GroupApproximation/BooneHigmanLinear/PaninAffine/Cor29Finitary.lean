import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.LocFinitary
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Localization.Integral

/-!
# The finitary step of LSV Cor 2.9 (lane k2-panin)

This module proves `Cor29FinitaryAt R P N` for every domain `R` and prime `P`. It is F.5
(Tulenbaev, Lemma 2.2) for polynomial rings over localizations. It combines `K2Found.Colimit`
with the divisibility-indexed system of `K2Found.LocFinitary`, replacing `A_a` by `A_a[X]`.
* `R_P[X]` is the colimit of the `R_a[X]`, `a ∉ P`. So every element of `St_N(R_P[X])` comes
  from some `St_N(R_a[X])` (`polyLift_surj`, `K2Found.exists_ringMap_eq`).
* `Frac(R)[X]` is the colimit of the `R_b[X]`, `b ≠ 0`, and here the cocone maps are injective.
  Let an element of `St_N(R_a[X])` die in `St_N(Frac(R)[X])`. Then it dies in some
  `St_N(R_{ah}[X])` with `h ≠ 0` (`K2Found.exists_ringMap_eq_one`), so it dies once `h` is
  inverted (`exists_ne_zero_death`).

So `eq_one_of_fracMap` holds without its finitary input: `eq_one_of_fracMap_of_geometry`.
Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigman GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found

section PolySystem

variable {A : Type} [CommRing A] (M : Submonoid A)

/-- `A_a[X] → A_b[X]` for `a ∣ b`. -/
noncomputable def polyMap (a b : DivIdx M) (h : a ≤ b) :
    Polynomial (Localization.Away a.val) →+* Polynomial (Localization.Away b.val) :=
  Polynomial.mapRingHom (divMap M a b h)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyMap

instance polySystem :
    DirectedSystem (fun a : DivIdx M => Polynomial (Localization.Away a.val))
      (fun a b h => polyMap M a b h) where
  map_self a z := by
    have h : divMap M a a le_rfl = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
        simp only [RingHom.comp_apply, divMap_algebraMap, RingHom.id_apply])
    show Polynomial.map (divMap M a a le_rfl) z = z
    rw [h, Polynomial.map_id]
  map_map c b a hab hbc z := by
    have h : (divMap M b c hbc).comp (divMap M a b hab) = divMap M a c (hab.trans hbc) :=
      IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
        simp only [RingHom.comp_apply, divMap_algebraMap])
    show Polynomial.map (divMap M b c hbc) (Polynomial.map (divMap M a b hab) z) =
      Polynomial.map (divMap M a c (hab.trans hbc)) z
    rw [Polynomial.map_map, h]

variable (S : Type) [CommRing S] [Algebra A S] [IsLocalization M S]

/-- `A_a[X] → S[X]` for `a ∈ M`. -/
noncomputable def polyLift (a : DivIdx M) : Polynomial (Localization.Away a.val) →+* Polynomial S :=
  Polynomial.mapRingHom (locLift M S a)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyLift

theorem polyLift_polyMap (a b : DivIdx M) (h : a ≤ b) (z : Polynomial (Localization.Away a.val)) :
    polyLift M S b (polyMap M a b h z) = polyLift M S a z := by
  have hc : (locLift M S b).comp (divMap M a b h) = locLift M S a :=
    RingHom.ext fun w => locLift_divMap M S a b h w
  show Polynomial.map (locLift M S b) (Polynomial.map (divMap M a b h) z) =
    Polynomial.map (locLift M S a) z
  rw [Polynomial.map_map, hc]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyLift_polyMap

/-- Every polynomial over `S` comes from some `A_a[X]`: clear denominators. -/
theorem polyLift_surj (p : Polynomial S) :
    ∃ a : DivIdx M, ∃ q : Polynomial (Localization.Away a.val), polyLift M S a q = p := by
  obtain ⟨b, hb, hP⟩ := IsLocalization.integerNormalization_spec M p
  obtain ⟨a, rfl⟩ : ∃ a : DivIdx M, a.val = b := ⟨⟨b, hb⟩, rfl⟩
  have hu : IsUnit (algebraMap A (Localization.Away a.val) a.val) :=
    IsLocalization.Away.algebraMap_isUnit a.val
  have hv : locLift M S a (↑hu.unit⁻¹) * algebraMap A S a.val = 1 := by
    rw [← locLift_algebraMap M S a a.val, ← map_mul, hu.val_inv_mul, map_one]
  refine ⟨a, Polynomial.C (↑hu.unit⁻¹ : Localization.Away a.val) *
    (IsLocalization.integerNormalization M p).map (algebraMap A (Localization.Away a.val)), ?_⟩
  ext n
  have h1 := congrArg (fun q => Polynomial.coeff q n) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul, Algebra.smul_def] at h1
  rw [polyLift, Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, locLift_comp, Polynomial.coeff_C_mul, Polynomial.coeff_map, h1,
    ← mul_assoc, hv, one_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyLift_surj

end PolySystem

section Death

/-- Let `u ∈ St_N(A_a[X])` die in `St_N(A_b[X])`, `a ∣ b`. Then `u` dies along every ring map
`A_a[X] → T` that makes `b` a unit. -/
theorem ringMap_eq_one_of_polyMap {A : Type} [CommRing A] {M : Submonoid A} {N : ℕ}
    (a b : DivIdx M) (hab : a ≤ b)
    {u : SteinbergGroup (Fin N) (Polynomial (Localization.Away a.val))}
    (hu : ringMap (polyMap M a b hab) u = 1) {T : Type} [CommRing T]
    (ρ : Polynomial (Localization.Away a.val) →+* T)
    (hρ : IsUnit (ρ (Polynomial.C (algebraMap A (Localization.Away a.val) b.val)))) :
    ringMap ρ u = 1 := by
  have hℓ : (IsLocalization.Away.lift (S := Localization.Away b.val) b.val
      (g := (ρ.comp Polynomial.C).comp (algebraMap A (Localization.Away a.val))) hρ).comp
        (divMap M a b hab) = ρ.comp Polynomial.C :=
    IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, divMap_algebraMap, IsLocalization.Away.lift_eq])
  have hfac : (Polynomial.eval₂RingHom (IsLocalization.Away.lift (S := Localization.Away b.val)
      b.val (g := (ρ.comp Polynomial.C).comp (algebraMap A (Localization.Away a.val))) hρ)
      (ρ Polynomial.X)).comp (polyMap M a b hab) = ρ := by
    apply Polynomial.ringHom_ext
    · intro z
      rw [RingHom.comp_apply, polyMap, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact RingHom.congr_fun hℓ z
    · rw [RingHom.comp_apply, polyMap, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [← hfac, ← SteinbergBasic.ringMap_ringMap, hu, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.ringMap_eq_one_of_polyMap

variable {R : Type} [CommRing R] [IsDomain R]

theorem locLift_frac_injective (a : DivIdx (nonZeroDivisors R)) :
    Function.Injective (locLift (nonZeroDivisors R) (FractionRing R) a) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj a.val z
  have h1 := congrArg (locLift (nonZeroDivisors R) (FractionRing R) a) hc
  rw [map_mul, hz, zero_mul, locLift_algebraMap] at h1
  have hc0 : c = 0 := IsFractionRing.injective R (FractionRing R)
    (h1.symm.trans (map_zero (algebraMap R (FractionRing R))).symm)
  rw [hc0, map_zero] at hc
  exact (((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a.val) a.val).pow
    n).mul_left_eq_zero).mp hc

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.locLift_frac_injective

theorem polyLift_frac_inj (a : DivIdx (nonZeroDivisors R))
    (z w : Polynomial (Localization.Away a.val))
    (h : polyLift (nonZeroDivisors R) (FractionRing R) a z =
      polyLift (nonZeroDivisors R) (FractionRing R) a w) :
    ∃ b, ∃ hab : a ≤ b, polyMap (nonZeroDivisors R) a b hab z =
      polyMap (nonZeroDivisors R) a b hab w := by
  have h' : Polynomial.map (locLift (nonZeroDivisors R) (FractionRing R) a) z =
      Polynomial.map (locLift (nonZeroDivisors R) (FractionRing R) a) w := h
  have hzw : z = w := Polynomial.map_injective _ (locLift_frac_injective a) h'
  exact ⟨a, le_rfl, by rw [hzw]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyLift_frac_inj

/-- **Death in `St_N(Frac(R)[X])` is witnessed by one `h ≠ 0`.** -/
theorem exists_ne_zero_death {N : ℕ} (b : DivIdx (nonZeroDivisors R))
    (v : SteinbergGroup (Fin N) (Polynomial (Localization.Away b.val)))
    (hv : ringMap (polyLift (nonZeroDivisors R) (FractionRing R) b) v = 1) :
    ∃ h : R, h ≠ 0 ∧ ringMap (Polynomial.mapRingHom (algebraMap (Localization.Away b.val)
      (Localization.Away (algebraMap R (Localization.Away b.val) h)))) v = 1 := by
  obtain ⟨j, hj, hdie⟩ := exists_ringMap_eq_one
    (R := fun a : DivIdx (nonZeroDivisors R) => Polynomial (Localization.Away a.val))
    (φ := polyMap (nonZeroDivisors R)) (polyLift (nonZeroDivisors R) (FractionRing R))
    (polyLift_polyMap (nonZeroDivisors R) (FractionRing R)) polyLift_frac_inj
    (polyLift_surj (nonZeroDivisors R) (FractionRing R)) hv
  obtain ⟨h, hh⟩ : b.val ∣ j.val := hj
  refine ⟨h, fun h0 => nonZeroDivisors.ne_zero j.mem (by rw [hh, h0, mul_zero]), ?_⟩
  refine ringMap_eq_one_of_polyMap b j hj hdie _ ?_
  rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.isUnit_C, hh, map_mul, map_mul]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val).map
    (algebraMap (Localization.Away b.val)
      (Localization.Away (algebraMap R (Localization.Away b.val) h)))).mul
    (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (algebraMap R (Localization.Away b.val) h)) _)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_ne_zero_death

end Death

section Finitary

variable {R : Type} [CommRing R] [IsDomain R]

theorem fracMap_algebraMap (P : Ideal R) [P.IsPrime] (r : R) :
    fracMap P (algebraMap R (Localization.AtPrime P) r) = algebraMap R (FractionRing R) r :=
  IsLocalization.lift_eq _ _

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fracMap_algebraMap

theorem locLift_fracMap (P : Ideal R) [P.IsPrime] (a : DivIdx P.primeCompl)
    (h0 : a.val ∈ nonZeroDivisors R) :
    (fracMap P).comp (locLift P.primeCompl (Localization.AtPrime P) a) =
      locLift (nonZeroDivisors R) (FractionRing R) ⟨a.val, h0⟩ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => ?_)
  show fracMap P (locLift P.primeCompl (Localization.AtPrime P) a (algebraMap R _ r)) =
    locLift (nonZeroDivisors R) (FractionRing R) ⟨a.val, h0⟩ (algebraMap R _ r)
  rw [locLift_algebraMap P.primeCompl (Localization.AtPrime P) a r, fracMap_algebraMap,
    locLift_algebraMap (nonZeroDivisors R) (FractionRing R) ⟨a.val, h0⟩ r]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.locLift_fracMap

theorem polyLift_fracMap (P : Ideal R) [P.IsPrime] (a : DivIdx P.primeCompl)
    (h0 : a.val ∈ nonZeroDivisors R) :
    (Polynomial.mapRingHom (fracMap P)).comp (polyLift P.primeCompl (Localization.AtPrime P) a) =
      polyLift (nonZeroDivisors R) (FractionRing R) ⟨a.val, h0⟩ := by
  unfold polyLift
  exact (Polynomial.mapRingHom_comp _ _).trans
    (congrArg Polynomial.mapRingHom (locLift_fracMap P a h0))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyLift_fracMap

/-- **F.5 for Cor 2.9.** -/
theorem cor29FinitaryAt (P : Ideal R) [P.IsPrime] (N : ℕ) : Cor29FinitaryAt R P N := by
  intro α hα
  obtain ⟨a, u, hu⟩ := exists_ringMap_eq
    (R := fun a : DivIdx P.primeCompl => Polynomial (Localization.Away a.val))
    (φ := polyMap P.primeCompl) (polyLift P.primeCompl (Localization.AtPrime P))
    (polyLift_polyMap P.primeCompl (Localization.AtPrime P))
    (polyLift_surj P.primeCompl (Localization.AtPrime P)) α
  have hg : a.val ∉ P := Ideal.mem_primeCompl_iff.mp a.mem
  have h0 : a.val ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero fun h => hg (h ▸ P.zero_mem)
  have hv : ringMap (polyLift (nonZeroDivisors R) (FractionRing R) ⟨a.val, h0⟩) u = 1 := by
    have h1 : ringMap (Polynomial.mapRingHom (fracMap P))
        (ringMap (polyLift P.primeCompl (Localization.AtPrime P) a) u) = 1 := by
      rw [hu]
      exact hα
    rw [SteinbergBasic.ringMap_ringMap, polyLift_fracMap P a h0] at h1
    exact h1
  obtain ⟨h, hh0, hdie⟩ := exists_ne_zero_death ⟨a.val, h0⟩ u hv
  exact ⟨a.val, hg, h, hh0, u, hu, hdie⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.cor29FinitaryAt

/-- **LSV Cor 2.9 (`m = 1`) for `K[s₁..s_k]`, finitary input discharged.** -/
theorem eq_one_of_fracMap_of_geometry {K : Type} [Field K] {k r : ℕ}
    (hGeo : AffineMonicFibreStatement K)
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal]
    (α : SteinbergGroup (Fin r) (Polynomial (Localization.AtPrime M)))
    (hα : ringMap (Polynomial.mapRingHom (fracMap M)) α = 1) : α = 1 :=
  eq_one_of_fracMap hGeo hExc hMon M (cor29FinitaryAt M r) α hα

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.eq_one_of_fracMap_of_geometry

end Finitary

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
