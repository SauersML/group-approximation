import GroupApproximation.Manuscript.OneSidedMFRadical.KappaFiniteWitness
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsMatrixReduction
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaResidue

/-!
# The canonical K₁ kernel theorem

This closes `AGPUnitKappa`, for the actual stable algebraic K₁ construction.
An arbitrary K₁-trivial unit reduces modulo commutators to a unit fixing a
nonzero idempotent. Its finite stabilized commutator witness can be compressed
back into R by a matrix-corner homomorphism that returns that supported unit.
Homomorphisms preserve commutators. Thus the unit itself is a commutator.
-/

namespace GroupApproximation
namespace KappaProof

open AlgebraicK RankNElimination MFQuotientUnits

section Compression

variable {R : Type*} [Ring R]

/-- Arbitrarily many mutually orthogonal copies of the unit, normalized to
matrix-coordinate witnesses. The sum need not be the whole unit. -/
theorem exists_coordinates (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      ∀ i j, i ≠ j → t i * s j = 0 := by
  obtain ⟨r, hr, hortho, hequiv⟩ := exists_orthogonal_unit_family hR n
  have hc : ∀ i : Fin n, ∃ s t : R, t * s = 1 ∧ s * t = r i := by
    intro i
    obtain ⟨s, t, hts, hst, -, -, -, -⟩ :=
      exists_normalized_isometry IsIdempotentElem.one (hr i)
        (one_mul _) (mul_one _) (hequiv i).symm
    exact ⟨s, t, hts, hst⟩
  choose s t hts hst using hc
  refine ⟨s, t, hts, ?_⟩
  intro i j hij
  have hs : r j * s j = s j := by rw [← hst j, mul_assoc, hts j, mul_one]
  have ht : t i * r i = t i := by rw [← hst i, ← mul_assoc, hts i, one_mul]
  calc t i * s j = (t i * r i) * (r j * s j) := by rw [ht, hs]
    _ = t i * (r i * r j) * s j := by noncomm_ring
    _ = 0 := by rw [hortho i j hij]; simp

theorem matrixEmbed_single {n : ℕ} (s t : Fin n → R) (i j : Fin n) (c : R) :
    matrixEmbed s t (Matrix.single i j c) = s i * c * t j := by
  classical
  simp [matrixEmbed, Matrix.single]

/-- Only the distinguished diagonal entry changes in a corner insertion. -/
theorem matrixCornerUnitHom_diagAt_val {n : ℕ} (s t : Fin n → R)
    (hts : ∀ i, t i * s i = 1)
    (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0)
    (l : Fin n) (v : Rˣ) :
    (matrixCornerUnitHom s t hts hcross (diagAt l v) : R) =
      1 - s l * t l + s l * (v : R) * t l := by
  classical
  have hdiag : (diagAt l v).val = 1 + Matrix.single l l ((v : R) - 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hil : i = l <;> simp [diagAt_val, Matrix.diagonal_apply, Matrix.single, hil]
    · simp [diagAt_val, Matrix.diagonal_apply, Matrix.single, hij]
  rw [coe_matrixCornerUnitHom, hdiag, matrixEmbed_add, matrixEmbed_one,
    matrixEmbed_single]
  noncomm_ring

/-- A supported unit whose diagonal is a commutator at any finite rank is
already a commutator in the original unit group. No countability is needed
for this algebraic compression step. -/
theorem supported_mem_commutator (hR : IsPurelyInfiniteSimpleRing R)
    (v : Rˣ) (e : R) (hne : e ≠ 0) (he : IsIdempotentElem e)
    (hvform : (v : R) = e + (1 - e) * (v : R) * (1 - e))
    {n : ℕ} (l : Fin n)
    (hdiag : diagAt l v ∈ commutator (Matrix (Fin n) (Fin n) R)ˣ) :
    v ∈ commutator Rˣ := by
  classical
  have hee : e * e = e := he
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ :=
    isInfiniteIdempotent_of_ne_zero hR he hne
  have hef : e * f = f := by rw [hsum, add_mul, hf, hgf, add_zero]
  have hfe : f * e = f := by rw [hsum, mul_add, hf, hfg, add_zero]
  have heg : e * g = g := by rw [hsum, add_mul, hfg, hg, zero_add]
  have hge : g * e = g := by rw [hsum, mul_add, hgf, hg, zero_add]
  obtain ⟨a, b, hba, hab, hea, hae, heb, hbe⟩ :=
    exists_normalized_isometry he hf hef hfe hequiv
  have hfa : f * a = a := by rw [← hab, mul_assoc, hba, hae]
  have hbf : b * f = b := by rw [← hab, ← mul_assoc, hba, heb]
  have hga : g * a = 0 := by
    have hh : g = e - f := by rw [hsum]; abel
    rw [hh, sub_mul, hea, hfa, sub_self]
  have hbg : b * g = 0 := by
    have hh : g = e - f := by rw [hsum]; abel
    rw [hh, mul_sub, hbe, hbf, sub_self]
  obtain ⟨x, y, hxy⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR hgne
  obtain ⟨S, T, hTS, hTC⟩ := exists_coordinates hR n
  let s : Fin n → R := fun i => if i = l then 1 - e + a else g * y * S i
  let t : Fin n → R := fun i => if i = l then 1 - e + b else T i * x * g
  have htail : ∀ i j, (T i * x * g) * (g * y * S j) = T i * S j := by
    intro i j
    calc (T i * x * g) * (g * y * S j) = T i * (x * (g * g) * y) * S j := by
          noncomm_ring
      _ = T i * S j := by rw [hg, hxy, mul_one]
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    by_cases hil : i = l
    · simp only [s, t, if_pos hil]
      simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
        hee, hea, hbe, hba]
      abel
    · simp only [s, t, if_neg hil, htail, hTS]
  have hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0 := by
    intro i j hij
    by_cases hil : i = l
    · have hjl : j ≠ l := fun h => hij (hil.trans h.symm)
      simp only [s, t, if_pos hil, if_neg hjl]
      have hz : (1 - e + b) * g = 0 := by
        rw [add_mul, sub_mul, one_mul, heg, hbg]; abel
      rw [← mul_assoc, ← mul_assoc, hz, zero_mul, zero_mul]
    · by_cases hjl : j = l
      · simp only [s, t, if_neg hil, if_pos hjl]
        have hz : g * (1 - e + a) = 0 := by
          rw [mul_add, mul_sub, mul_one, hge, hga]; abel
        rw [mul_assoc, hz, mul_zero]
      · simp only [s, t, if_neg hil, if_neg hjl, htail, hTC i j hij]
  have hev : e * (v : R) = e := by
    calc e * (v : R) = e * (e + (1 - e) * (v : R) * (1 - e)) :=
        congrArg (e * ·) hvform
      _ = e := by rw [mul_add, he, ← mul_assoc, ← mul_assoc,
        he.mul_one_sub_self, zero_mul, zero_mul, add_zero]
  have hve : (v : R) * e = e := by
    calc (v : R) * e = (e + (1 - e) * (v : R) * (1 - e)) * e :=
        congrArg (· * e) hvform
      _ = e := by rw [add_mul, he, mul_assoc, he.one_sub_mul_self,
        mul_zero, add_zero]
  have hav : a * (v : R) = a := by
    calc a * (v : R) = (a * e) * (v : R) := by rw [hae]
      _ = a := by rw [mul_assoc, hev, hae]
  have hvb : (v : R) * b = b := by
    calc (v : R) * b = (v : R) * (e * b) := by rw [heb]
      _ = b := by rw [← mul_assoc, hve, heb]
  have hst : s l * t l = 1 - e + f := by
    simp only [s, t, ite_true]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      hee, heb, hae, hab]
    abel
  have hreturn : s l * (v : R) * t l = (v : R) - e + f := by
    simp only [s, t, ite_true]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      hev, hve, hav, hvb, hee, heb, hae, hab]
    abel
  have hunit : matrixCornerUnitHom s t hts hcross (diagAt l v) = v := by
    apply Units.ext
    rw [matrixCornerUnitHom_diagAt_val, hst, hreturn]
    abel
  rw [← hunit]
  exact map_mem_commutator _ hdiag

end Compression

section CanonicalKernel

variable (R : Type) [Ring R] [Countable R]

/-- The difficult containment in the canonical algebraic K₁ kernel theorem. -/
theorem kappa_ker_le_commutator (hR : IsPurelyInfiniteSimpleRing R) :
    (kappa R).ker ≤ commutator Rˣ := by
  haveI : Countable Rˣ := Function.Injective.countable
    (f := (Units.val : Rˣ → R)) (fun _ _ h => Units.ext h)
  have hC : cornerUnitSubgroup R ≤ commutator Rˣ :=
    (cornerUnitSubgroup_le_mfHomKernel
      Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
      R).trans (MFQuotientMatrices.mfHomKernel_le_commutator Rˣ)
  intro u hu
  obtain ⟨v, e, hne, he, hvform, huv⟩ := unit_reduces_to_supported hR u
  have hdelta := hC huv
  have hkdelta := MFQuotientUnitsKOne.commutator_le_kappa_ker R hdelta
  have hkv : kappa R v = 1 := by
    change kappa R (u * v⁻¹) = 1 at hkdelta
    change kappa R u = 1 at hu
    rw [map_mul, map_inv, hu, one_mul, inv_eq_one] at hkdelta
    exact hkdelta
  obtain ⟨n, hn, hdiag⟩ := exists_diagonal_mem_commutator R hR v hkv
  have hvcomm := supported_mem_commutator hR v e hne he hvform ⟨0, hn⟩ hdiag
  have hm := (commutator Rˣ).mul_mem hdelta hvcomm
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

end CanonicalKernel
end KappaProof

namespace MFQuotientUnitsKOne

open AlgebraicK MFQuotientUnits

/-- **Ara--Goodearl--Pardo's canonical K₁ identification**, proved for every
countable purely infinite simple ring. No AGP input proposition remains. -/
theorem agpUnitKappa : AGPUnitKappa := by
  intro R _ _ hR
  haveI := hR.isSimpleRing
  exact ⟨kappa_surjective (fun a ha => exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha),
    le_antisymm (KappaProof.kappa_ker_le_commutator R hR) (commutator_le_kappa_ker R)⟩

/-- The rank-one canonical maximal MF quotient and its unique factorization
property, with all inputs discharged. -/
theorem manuscriptMFQuotientUnitsKOne : PrintedMFQuotientUnitsKOne :=
  printedMFQuotientUnitsKOne_of_agp agpUnitKappa agpMenalMoncasiReduction agpStepOne

/-- The canonical K₁ quotient of each matrix ring, with all inputs discharged. -/
theorem manuscriptMFQuotientUnitsKOneAllRanks : PrintedMFQuotientUnitsKOneAllRanks :=
  printedMFQuotientUnitsKOneAllRanks_of_agpThree
    agpUnitKappa agpMenalMoncasiReduction agpStepOne

end MFQuotientUnitsKOne
end GroupApproximation

#audit_axioms GroupApproximation.KappaProof.supported_mem_commutator
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappa
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAllRanks
