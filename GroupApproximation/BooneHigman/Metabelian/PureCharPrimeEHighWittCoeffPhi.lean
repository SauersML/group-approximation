import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffLoc
import GroupApproximation.Meta.AxiomGuard

/-!
# The injective ring map `D → W₂(L)` (bh-met-87e, part 4)

We build `g : ZMod (p²)[σ] →+* W₂(L)`, where `L = Frac(𝔽_p[σ])`. It is the `ZMod (p²)`-structure
map (`W₂(L)` has characteristic `p²`, `eHighWittCoeff_charP_W`) together with `X s ↦ (X s, 0)`.
Its zeroth coordinate is `algebraMap ∘ red` (`eHighWittCoeff_g_x0`). Hence:
* `g` sends `S` to units (`eHighWittCoeff_isUnit`);
* `g` is injective (`eHighWittCoeff_g_injective`). If `g a = 0`, then `red a = 0`, so `a = p b`.
  Then `0 = g (p b) = (0, (g b)₀^p)` gives `red b = 0`, so `b = p c` and `a = p² c = 0`.

The lift `φ : D = S⁻¹ D₀ →+* W₂(L)` (`eHighWittCoeff_phi`) is injective
(`eHighWittCoeff_phi_injective`). This is the ring side of `EHighWittLinCoeffStatement`, proved
outright. Perfectness of `L` is not used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable (p : ℕ) (σ : Type)

/-- The structure map `ZMod (p²) → W₂(L)`. -/
def eHighWittCoeff_f0 [Fact p.Prime] : ZMod (p ^ 2) →+* eHighWitt_W2 (eHighWittCoeff_L p σ) p :=
  ZMod.castHom (dvd_refl (p ^ 2)) (eHighWitt_W2 (eHighWittCoeff_L p σ) p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_f0

/-- The images `X s ↦ (X s, 0)` of the variables. -/
def eHighWittCoeff_gX [Fact p.Prime] : σ → eHighWitt_W2 (eHighWittCoeff_L p σ) p :=
  fun s => eHighWitt_W2.mk (algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ)
    (MvPolynomial.X s)) 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_gX

/-- The ring map `g : ZMod (p²)[σ] →+* W₂(L)`. -/
def eHighWittCoeff_g [Fact p.Prime] :
    MvPolynomial σ (ZMod (p ^ 2)) →+* eHighWitt_W2 (eHighWittCoeff_L p σ) p :=
  MvPolynomial.eval₂Hom (eHighWittCoeff_f0 p σ) (eHighWittCoeff_gX p σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_g

/-- The zeroth coordinate of `g` is `algebraMap ∘ red`, as ring maps. -/
theorem eHighWittCoeff_g_x0_hom [Fact p.Prime] :
    (eHighWittCoeff_x0Hom (L := eHighWittCoeff_L p σ) (p := p)).comp (eHighWittCoeff_g p σ) =
      (algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ)).comp
        (eHighWittCoeff_red p σ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_zmod
      (((eHighWittCoeff_x0Hom (L := eHighWittCoeff_L p σ) (p := p)).comp
        (eHighWittCoeff_g p σ)).comp MvPolynomial.C)
      (((algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ)).comp
        (eHighWittCoeff_red p σ)).comp MvPolynomial.C)) r
  · show (eHighWittCoeff_g p σ (MvPolynomial.X i)).x0 =
      algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ)
        (eHighWittCoeff_red p σ (MvPolynomial.X i))
    rw [eHighWittCoeff_red, MvPolynomial.map_X]
    exact congrArg eHighWitt_W2.x0
      (MvPolynomial.eval₂Hom_X' (eHighWittCoeff_f0 p σ) (eHighWittCoeff_gX p σ) i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_g_x0_hom

theorem eHighWittCoeff_g_x0 [Fact p.Prime] (a : MvPolynomial σ (ZMod (p ^ 2))) :
    (eHighWittCoeff_g p σ a).x0 =
      algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ) (eHighWittCoeff_red p σ a) :=
  RingHom.congr_fun (eHighWittCoeff_g_x0_hom p σ) a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_g_x0

/-- `g` sends `S` to units. -/
theorem eHighWittCoeff_g_isUnit [Fact p.Prime] (s : eHighWittCoeff_S p σ) :
    IsUnit (eHighWittCoeff_g p σ s) := by
  refine eHighWittCoeff_isUnit ?_
  rw [eHighWittCoeff_g_x0]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (R := MvPolynomial σ (ZMod p))
    (K := eHighWittCoeff_L p σ) s.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_g_isUnit

theorem eHighWittCoeff_red_of_x0 [Fact p.Prime] {a : MvPolynomial σ (ZMod (p ^ 2))}
    (h : (eHighWittCoeff_g p σ a).x0 = 0) : eHighWittCoeff_red p σ a = 0 := by
  rw [eHighWittCoeff_g_x0] at h
  exact IsFractionRing.injective (R := MvPolynomial σ (ZMod p)) (K := eHighWittCoeff_L p σ)
    (h.trans (map_zero (algebraMap (MvPolynomial σ (ZMod p)) (eHighWittCoeff_L p σ))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_red_of_x0

/-- **`g` is injective.** -/
theorem eHighWittCoeff_g_injective [Fact p.Prime] :
    Function.Injective (eHighWittCoeff_g p σ) := by
  have hp : p.Prime := Fact.out
  refine (injective_iff_map_eq_zero (eHighWittCoeff_g p σ)).mpr fun a ha => ?_
  obtain ⟨b, rfl⟩ := eHighWittCoeff_red_eq_zero p σ
    (eHighWittCoeff_red_of_x0 p σ (congrArg eHighWitt_W2.x0 ha))
  rw [map_mul, map_natCast, eHighWittCoeff_p_mul] at ha
  have h1 : (eHighWittCoeff_g p σ b).x0 ^ p = 0 := congrArg eHighWitt_W2.x1 ha
  obtain ⟨c, rfl⟩ := eHighWittCoeff_red_eq_zero p σ
    (eHighWittCoeff_red_of_x0 p σ ((pow_eq_zero_iff hp.ne_zero).mp h1))
  have hpp : ((p * p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) = 0 :=
    (CharP.cast_eq_zero_iff (MvPolynomial σ (ZMod (p ^ 2))) (p ^ 2) (p * p)).mpr ⟨1, by ring⟩
  rw [← mul_assoc, ← Nat.cast_mul, hpp, zero_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_g_injective

/-- **The ring map `φ : D →+* W₂(L)`**, lifting `g` from `D₀` to `D = S⁻¹ D₀`. -/
def eHighWittCoeff_phi [Fact p.Prime] :
    eHighWittCoeff_D p σ →+* eHighWitt_W2 (eHighWittCoeff_L p σ) p :=
  IsLocalization.lift (M := eHighWittCoeff_S p σ) (S := eHighWittCoeff_D p σ)
    (eHighWittCoeff_g_isUnit p σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_phi

/-- **`φ` is injective.** -/
theorem eHighWittCoeff_phi_injective [Fact p.Prime] :
    Function.Injective (eHighWittCoeff_phi p σ) := by
  refine (injective_iff_map_eq_zero (eHighWittCoeff_phi p σ)).mpr fun z hz => ?_
  obtain ⟨x, hx⟩ := IsLocalization.surj (eHighWittCoeff_S p σ) z
  have h0 := congrArg (eHighWittCoeff_phi p σ) hx
  rw [map_mul, hz, zero_mul] at h0
  have h1 : eHighWittCoeff_g p σ x.1 = 0 :=
    (IsLocalization.lift_eq (S := eHighWittCoeff_D p σ) (eHighWittCoeff_g_isUnit p σ)
      x.1).symm.trans h0.symm
  have h2 : x.1 = 0 :=
    eHighWittCoeff_g_injective p σ (h1.trans (map_zero (eHighWittCoeff_g p σ)).symm)
  rw [h2, map_zero] at hx
  exact (IsLocalization.map_units (eHighWittCoeff_D p σ) x.2).mul_left_eq_zero.mp hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_phi_injective

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
