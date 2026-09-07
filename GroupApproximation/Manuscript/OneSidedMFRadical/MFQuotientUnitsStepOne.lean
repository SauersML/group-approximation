import GroupApproximation.Algebra.CornerUnitExtension
import GroupApproximation.Algebra.PurelyInfiniteWholeRingCornerUnits
import GroupApproximation.Algebra.PurelyInfiniteMatrixEmbedding
import GroupApproximation.KOne.BlockWhitehead
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnits

/-!
# The supported-unit step in the MF quotient theorem

This module discharges `MFQuotientUnits.AGPStepOne`. A commutator-subgroup
unit that fixes a nonzero idempotent belongs to the corner-unit subgroup.

Only two matrix coordinates are needed: Whitehead already sends the entire
unit commutator subgroup into `EL₂(R)`. Shrink the fixed idempotent e to an
equivalent f, use the nonzero remainder e-f for a second copy of R, and
extend the resulting matrix-corner units by the complementary identity.
On `diag(v,1)` this homomorphism returns v itself.

The other AGP step, which moves an arbitrary unit to this supported form,
and the identification with canonical algebraic K₁ are separate statements.
-/

namespace GroupApproximation
namespace MFQuotientUnits

section Idempotents

variable {R : Type*} [Ring R]

/-- An idempotent containing an infinite idempotent is itself infinite. -/
theorem isInfiniteIdempotent_of_le {e p : R} (he : IsIdempotentElem e)
    (hp : IsIdempotentElem p) (hpe : IdempotentLE p e)
    (hinf : IsInfiniteIdempotent R p) : IsInfiniteIdempotent R e := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ := hinf
  have hpf : p * f = f := by rw [hsum, add_mul, hf, hgf, add_zero]
  have hfp : f * p = f := by rw [hsum, mul_add, hf, hfg, add_zero]
  have hpg : p * g = g := by rw [hsum, add_mul, hfg, hg, zero_add]
  have hgp : g * p = g := by rw [hsum, mul_add, hgf, hg, zero_add]
  obtain ⟨s, t, hts, hst, hps, hsp, hpt, htp⟩ :=
    exists_normalized_isometry hp hf hpf hfp hequiv
  let q := e - p
  have hq : IsIdempotentElem q := isIdempotentElem_sub he hp hpe
  have hqp : q * p = 0 := sub_mul_self_eq_zero hp hpe
  have hpq : p * q = 0 := by dsimp [q]; rw [mul_sub, hpe.2, hp, sub_self]
  have hzleft : ∀ a : R, p * a = a → q * a = 0 := by
    intro a ha
    calc q * a = q * (p * a) := by rw [ha]
      _ = 0 := by rw [← mul_assoc, hqp, zero_mul]
  have hzright : ∀ a : R, a * p = a → a * q = 0 := by
    intro a ha
    calc a * q = (a * p) * q := by rw [ha]
      _ = 0 := by rw [mul_assoc, hpq, mul_zero]
  have hqf := hzleft f hpf
  have hfq := hzright f hfp
  have hqg := hzleft g hpg
  have hgq := hzright g hgp
  have hqs := hzleft s hps
  have hsq := hzright s hsp
  have hqt := hzleft t hpt
  have htq := hzright t htp
  refine ⟨f + q, g, ?_, hg, ?_, ?_, ?_, ?_, hgne⟩
  · show (f + q) * (f + q) = f + q
    simp only [add_mul, mul_add, hf, hq, hfq, hqf, add_zero, zero_add]
  · rw [add_mul, hfg, hqg, add_zero]
  · rw [mul_add, hgf, hgq, add_zero]
  · dsimp [q]; rw [hsum]; abel
  · refine ⟨t + q, s + q, ?_, ?_⟩
    · rw [add_mul, mul_add, mul_add, hts, htq, hqs, hq]
      dsimp [q]; abel
    · rw [add_mul, mul_add, mul_add, hst, hsq, hqt, hq]
      abel

/-- Every nonzero idempotent of a purely infinite simple ring is infinite.
The right-ideal witness is normalized into a two-sided sub-idempotent. -/
theorem isInfiniteIdempotent_of_ne_zero (hR : IsPurelyInfiniteSimpleRing R)
    {e : R} (he : IsIdempotentElem e) (hne : e ≠ 0) :
    IsInfiniteIdempotent R e := by
  obtain ⟨p, r, hpr, hp, hpinf⟩ := hR.exists_infiniteIdempotent hne
  have hep : e * p = p := by rw [hpr, ← mul_assoc, he]
  have hpe : IsIdempotentElem (p * e) := by
    show p * e * (p * e) = p * e
    rw [mul_assoc p e, ← mul_assoc e p, hep, ← mul_assoc, hp]
  have hle : IdempotentLE (p * e) e := by
    constructor
    · rw [← mul_assoc, hep]
    · rw [mul_assoc, he]
  have hequiv : IsEquivalentIdempotent R (p * e) p :=
    ⟨p, e, rfl, hep.symm⟩
  exact isInfiniteIdempotent_of_le he hpe hle
    (IsInfiniteIdempotent.of_equivalent hpe hequiv hpinf)

end Idempotents

section MatrixCorner

variable {R : Type*} [Ring R] {n : ℕ} (s t : Fin n → R)
variable (hts : ∀ i, t i * s i = 1)
variable (hcross : ∀ i j : Fin n, i ≠ j → t i * s j = 0)

/-- Package the matrix embedding as a unital homomorphism to its own corner. -/
noncomputable def matrixCornerHom :
    Matrix (Fin n) (Fin n) R →+*
      Corner R (matrixWitnessSum s t) (isIdempotentElem_matrixWitnessSum hts hcross) where
  toFun A := ⟨matrixEmbed s t A, matrixEmbed_mem_corner hts hcross A⟩
  map_one' := corner_ext matrixEmbed_one
  map_mul' A B := corner_ext (matrixEmbed_mul hts hcross A B)
  map_zero' := corner_ext (by simp [matrixEmbed])
  map_add' A B := corner_ext (matrixEmbed_add A B)

/-- Matrix units become whole-ring units by adding the complementary identity. -/
noncomputable def matrixCornerUnitHom : (Matrix (Fin n) (Fin n) R)ˣ →* Rˣ :=
  (unitOfCornerUnit (matrixWitnessSum s t)
    (isIdempotentElem_matrixWitnessSum hts hcross)).comp
      (Units.map (matrixCornerHom s t hts hcross).toMonoidHom)

@[simp] theorem coe_matrixCornerUnitHom (A : (Matrix (Fin n) (Fin n) R)ˣ) :
    ((matrixCornerUnitHom s t hts hcross A : Rˣ) : R) =
      1 - matrixWitnessSum s t + matrixEmbed s t (A : Matrix (Fin n) (Fin n) R) := rfl

end MatrixCorner

section SupportedUnits

variable {R : Type} [Ring R] [Countable R]

/-- Whitehead sends the entire unit commutator subgroup into `EL₂`, already
at rank two; no choice of a stabilization rank is necessary. -/
omit [Countable R] in
theorem diag_mem_elementary_of_mem_commutator {v : Rˣ}
    (hv : v ∈ commutator Rˣ) :
    RankNElimination.diagAt (0 : Fin 2) v ∈ elementaryGroup (Fin 2) R := by
  have hle : commutator Rˣ ≤
      (elementaryGroup (Fin 2) R).comap (RankNElimination.diagAtHom (0 : Fin 2)) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact RankNElimination.diagAt_commutatorElement_mem (0 : Fin 2) 1 (by decide) a b
  exact hle hv

/-- **The supported-unit step**, with its actual group-theoretic hypothesis. -/
theorem supported_commutator_mem_cornerUnitSubgroup
    (hR : IsPurelyInfiniteSimpleRing R) (v : Rˣ) (e : R)
    (hne : e ≠ 0) (he : IsIdempotentElem e)
    (hvform : (v : R) = e + (1 - e) * (v : R) * (1 - e))
    (hvcomm : v ∈ commutator Rˣ) : v ∈ cornerUnitSubgroup R := by
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
  let s : Fin 2 → R := ![1 - e + a, g * y]
  let t : Fin 2 → R := ![1 - e + b, x * g]
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    fin_cases i
    · change (1 - e + b) * (1 - e + a) = 1
      simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
        he, hea, hbe, hba]
      abel
    · change (x * g) * (g * y) = 1
      rw [mul_assoc x g, ← mul_assoc g g, hg, ← mul_assoc, hxy]
  have hcross : ∀ i j : Fin 2, i ≠ j → t i * s j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (1 - e + b) * (g * y) = 0
      rw [← mul_assoc, add_mul, sub_mul, one_mul, heg, hbg]
      simp
    · change (x * g) * (1 - e + a) = 0
      rw [mul_assoc, mul_add, mul_sub, mul_one, hge, hga]
      simp
    · exact (hij rfl).elim
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
  have hst0 : s 0 * t 0 = 1 - e + f := by
    change (1 - e + a) * (1 - e + b) = 1 - e + f
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      he, heb, hae, hab]
    abel
  have hdiag0 : s 0 * (v : R) * t 0 = (v : R) - e + f := by
    change (1 - e + a) * (v : R) * (1 - e + b) = (v : R) - e + f
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
      hev, hve, hav, hvb, he, heb, hae, hab]
    abel
  let φ := (matrixCornerUnitHom s t hts hcross).comp
    (elementaryGroup (Fin 2) R).subtype
  have hdiag := diag_mem_elementary_of_mem_commutator hvcomm
  have hreturn : φ ⟨RankNElimination.diagAt (0 : Fin 2) v, hdiag⟩ = v := by
    apply Units.ext
    change 1 - matrixWitnessSum s t +
      matrixEmbed s t (RankNElimination.diagAt (0 : Fin 2) v).val = (v : R)
    simp only [matrixWitnessSum, matrixEmbed, Fin.sum_univ_two,
      RankNElimination.diagAt_val, Matrix.diagonal_apply]
    simp only [ite_true, ite_false, Fin.zero_ne_one, Fin.one_ne_zero,
      mul_zero, zero_mul, mul_one, add_zero, zero_add]
    rw [hst0, hdiag0]
    abel
  exact elementaryRange_le_cornerUnitSubgroup hR (by decide : 2 ≤ 2) φ
    ⟨⟨RankNElimination.diagAt (0 : Fin 2) v, hdiag⟩, hreturn⟩

end SupportedUnits

/-- **AGP Step 1 as consumed by the manuscript**, discharged. -/
theorem agpStepOne : AGPStepOne := by
  intro R _ _ hR A _ κ _ hker v e hne he hvform hkv
  apply supported_commutator_mem_cornerUnitSubgroup hR v e hne he hvform
  rw [← hker]
  exact hkv

end MFQuotientUnits
end GroupApproximation

#audit_closed_axioms GroupApproximation.MFQuotientUnits.agpStepOne
#audit_axioms GroupApproximation.MFQuotientUnits.supported_commutator_mem_cornerUnitSubgroup
