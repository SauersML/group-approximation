import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseDenominators
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local case, part 2: what dies in `M⁻¹A` dies in some `A_{a c}`

Lane `bh-met-88`.  For `S = M⁻¹A` and `a ∈ M`: an element, a polynomial, and an invertible
polynomial matrix over `A_a` whose image in `S` vanishes (resp. two whose images agree) already
vanish (resp. agree) in `A_{a c}` whenever `b ∣ c`, for a suitable `b ∈ M`.  This is the
elementwise half of clearing denominators.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- An element of `A_a` that dies in `S` dies in `A_{a c}` for all `c` divisible by some
`b ∈ M`. -/
theorem suslinLocalCase_eventually_zero (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a : A} (ha : a ∈ M) {z : Localization.Away a}
    (hz : suslinLocalCase_toLoc S ha z = 0) :
    ∃ b ∈ M, ∀ c : A, b ∣ c → suslinLocalCase_trans (dvd_mul_right a c) z = 0 := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj a z
  have hx0 : algebraMap A S x = 0 := by
    rw [← suslinLocalCase_toLoc_algebraMap S ha x, ← hx, map_mul, hz, zero_mul]
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M S x).1 hx0
  refine ⟨m, m.2, fun c hc ↦ ?_⟩
  have hmu : IsUnit (algebraMap A (Localization.Away (a * c)) m) :=
    IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (a * c)) (a * c)
      (hc.trans (dvd_mul_left c a))
  have hau : IsUnit (algebraMap A (Localization.Away (a * c)) a) :=
    IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (a * c)) (a * c)
      (dvd_mul_right a c)
  have hxc : algebraMap A (Localization.Away (a * c)) x = 0 :=
    hmu.mul_right_eq_zero.1 (by rw [← map_mul, hm, map_zero])
  have h := congrArg (suslinLocalCase_trans (dvd_mul_right a c)) hx
  rw [map_mul, map_pow, suslinLocalCase_trans_algebraMap, suslinLocalCase_trans_algebraMap,
    hxc] at h
  exact (hau.pow n).mul_left_eq_zero.1 h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_eventually_zero

/-- Two polynomials over `A_a` with the same image over `S` agree over `A_{a c}` for all `c`
divisible by some `b ∈ M`. -/
theorem suslinLocalCase_eventually_poly (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {a : A} (ha : a ∈ M)
    {p q : Polynomial (Localization.Away a)}
    (hpq : Polynomial.map (suslinLocalCase_toLoc S ha) p =
      Polynomial.map (suslinLocalCase_toLoc S ha) q) :
    ∃ b ∈ M, ∀ c : A, b ∣ c →
      Polynomial.map (suslinLocalCase_trans (dvd_mul_right a c)) p =
        Polynomial.map (suslinLocalCase_trans (dvd_mul_right a c)) q := by
  obtain ⟨b, hb, hbP⟩ := suslinLocalCase_eventually_finset M (p - q).support
    (fun n c ↦ suslinLocalCase_trans (dvd_mul_right a c) ((p - q).coeff n) = 0)
    fun n _ ↦ suslinLocalCase_eventually_zero S ha (by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, hpq, sub_self, Polynomial.coeff_zero])
  refine ⟨b, hb, fun c hc ↦ ?_⟩
  rw [← sub_eq_zero, ← Polynomial.map_sub]
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ∈ (p - q).support
  · exact hbP c hc n hn
  · rw [Polynomial.notMem_support_iff.1 hn, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_eventually_poly

/-- Two invertible polynomial matrices over `A_a` with the same image over `S` agree over
`A_{a c}` for all `c` divisible by some `b ∈ M`. -/
theorem suslinLocalCase_eventually_units_eq (S : Type*) [CommRing S] [Algebra A S]
    {M : Submonoid A} [IsLocalization M S] {N : ℕ} {a : A} (ha : a ∈ M)
    {g h : Matrix.GeneralLinearGroup (Fin N) (Polynomial (Localization.Away a))}
    (hgh : elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha)) g =
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha)) h) :
    ∃ b ∈ M, ∀ c : A, b ∣ c →
      elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (suslinLocalCase_trans (dvd_mul_right a c))) g =
        elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (suslinLocalCase_trans (dvd_mul_right a c))) h := by
  have hent : ∀ ij ∈ (Finset.univ : Finset (Fin N × Fin N)),
      Polynomial.map (suslinLocalCase_toLoc S ha)
          ((g : Matrix (Fin N) (Fin N) (Polynomial (Localization.Away a))) ij.1 ij.2) =
        Polynomial.map (suslinLocalCase_toLoc S ha)
          ((h : Matrix (Fin N) (Fin N) (Polynomial (Localization.Away a))) ij.1 ij.2) := by
    intro ij _
    rw [← suslinLocalCase_entry, ← suslinLocalCase_entry, hgh]
  obtain ⟨b, hb, hbP⟩ := suslinLocalCase_eventually_finset M
    (Finset.univ : Finset (Fin N × Fin N))
    (fun ij c ↦ Polynomial.map (suslinLocalCase_trans (dvd_mul_right a c))
        ((g : Matrix (Fin N) (Fin N) (Polynomial (Localization.Away a))) ij.1 ij.2) =
      Polynomial.map (suslinLocalCase_trans (dvd_mul_right a c))
        ((h : Matrix (Fin N) (Fin N) (Polynomial (Localization.Away a))) ij.1 ij.2))
    fun ij hij ↦ suslinLocalCase_eventually_poly S ha (hent ij hij)
  refine ⟨b, hb, fun c hc ↦ Units.ext (Matrix.ext fun i j ↦ ?_)⟩
  rw [suslinLocalCase_entry, suslinLocalCase_entry]
  exact hbP c hc (i, j) (Finset.mem_univ _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_eventually_units_eq

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
