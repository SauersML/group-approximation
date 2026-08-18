import GroupApproximation.Sofic.LiteralP13HodgeData
import GroupApproximation.Sofic.LiteralP13HodgePairTable
import GroupApproximation.Sofic.LiteralP13HodgeReplay

/-!
# Kernel-checked core of the exact P13 Hodge certificate

Every coefficient is computed directly from `LiteralP13HodgeData.D`, `.B`,
and `.q`.  The only finite acceleration is the sparse support-pair partition,
whose equality with the replayed product table is proved separately.
-/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

open ExactHodgeCertificate FiniteSupportHodgeCertificate
open LiteralP13HodgeData LiteralP13Presentation
open scoped BigOperators

noncomputable section

/-- A bounded-depth decomposition of the 102-row scalar product. -/
def gramPairNumerator (i k : Fin 6) (pair : Fin 22 × Fin 22) : ℤ :=
  (∑ block : Fin 12, ∑ offset : Fin 8,
    let row : Fin 102 := Fin.castAdd 6 (finProdFinEquiv (block, offset))
    qNumerator row i pair.1 * qNumerator row k pair.2) +
  ∑ offset : Fin 6,
    let row : Fin 102 := Fin.natAdd 96 offset
    qNumerator row i pair.1 * qNumerator row k pair.2

/-- Direct integer numerator of the exact Gram product `q⁺q`. -/
def gramNumerator (i k : Fin 6) (c : Fin 293) : ℤ :=
  ∑ pair ∈ LiteralP13HodgePairTable.classPairs c,
    gramPairNumerator i k pair

private theorem sum_fin102_chunks (f : Fin 102 → ℤ) :
    ∑ row, f row =
      (∑ block : Fin 12, ∑ offset : Fin 8,
        f (Fin.castAdd 6 (finProdFinEquiv (block, offset)))) +
      ∑ offset : Fin 6, f (Fin.natAdd 96 offset) := by
  rw [Fin.sum_univ_add (a := 96) (b := 6)]
  refine congrArg₂ (fun a b : ℤ ↦ a + b) ?_ rfl
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv
    (fun x : Fin 12 × Fin 8 ↦ f (Fin.castAdd 6 (finProdFinEquiv x)))
    (fun row : Fin 96 ↦ f (Fin.castAdd 6 row)) (fun _ ↦ rfl)).symm

/-- Direct integer numerator of the degree-one Hodge coefficient. -/
def hodgeNumerator (i k : Fin 6) (c : Fin 293) : ℤ :=
  ∑ pair ∈ LiteralP13HodgePairTable.classPairs c,
    ((∑ relator : Fin 13,
      LiteralP13HodgeReplay.boundaryNumerator relator i pair.1 *
        LiteralP13HodgeReplay.boundaryNumerator relator k pair.2) +
      LiteralP13HodgeData.adjointCoboundaryNumerator i pair.1 *
        LiteralP13HodgeData.adjointCoboundaryNumerator k pair.2)

/-- Exact integer numerator of `Δ₁ - (1/250)I - q⁺q`, at denominator `10^16`. -/
def residualNumerator (i k : Fin 6) (c : Fin 293) : ℤ :=
  hodgeNumerator i k c * 10000000000000000 -
    (if i = k ∧ c = 201 then 40000000000000 else 0) -
    gramNumerator i k c

def residualCoefficient (i k : Fin 6) (c : Fin 293) : ℚ :=
  (residualNumerator i k c : ℚ) / 10000000000000000

theorem gramCoefficient_eq_direct (i k : Fin 6) (c : Fin 293) :
    gramCoefficient LiteralP13HodgeReplay.productClassIndex
      LiteralP13HodgeData.qCoefficient i k c =
      (gramNumerator i k c : ℚ) / 10000000000000000 := by
  unfold gramCoefficient LiteralP13HodgeData.qCoefficient gramNumerator
  simp_rw [convolution_int_div]
  have hconv (row : Fin 102) :
      integerConvolution LiteralP13HodgeReplay.productClassIndex
          (qNumerator row i) (qNumerator row k) c =
        ∑ pair ∈ LiteralP13HodgePairTable.classPairs c,
          qNumerator row i pair.1 * qNumerator row k pair.2 := by
    exact LiteralP13HodgePairTable.integerConvolution_eq_classPairs
      (qNumerator row i) (qNumerator row k) c
  have hpairsQ :
      (∑ pair ∈ LiteralP13HodgePairTable.classPairs c,
        ∑ row : Fin 102,
          (qNumerator row i pair.1 : ℚ) * qNumerator row k pair.2) =
        ∑ pair ∈ LiteralP13HodgePairTable.classPairs c,
          (gramPairNumerator i k pair : ℚ) := by
    apply Finset.sum_congr rfl
    intro pair hpair
    norm_cast
    exact sum_fin102_chunks _
  simp_rw [hconv]
  rw [← Finset.sum_div]
  push_cast
  rw [Finset.sum_comm]
  rw [hpairsQ]
  norm_num [qDenominator]

theorem hodgeCoefficient_eq_direct (i k : Fin 6) (c : Fin 293) :
    hodgeCoefficient LiteralP13HodgeReplay.productClassIndex
      LiteralP13HodgeData.boundaryCoefficient
      LiteralP13HodgeData.adjointCoboundaryCoefficient i k c =
      (hodgeNumerator i k c : ℚ) := by
  unfold hodgeCoefficient LiteralP13HodgeData.boundaryCoefficient
    LiteralP13HodgeData.adjointCoboundaryCoefficient hodgeNumerator
  unfold convolution
  simp_rw [LiteralP13HodgePairTable.convolution_eq_classPairs]
  push_cast
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]

theorem scalarCoefficient_eq_direct (i k : Fin 6) (c : Fin 293) :
    scalarCoefficient 201 (1 / 250) i k c =
      ((if i = k ∧ c = 201 then 40000000000000 else 0 : ℤ) : ℚ) /
        10000000000000000 := by
  unfold scalarCoefficient
  by_cases h : i = k ∧ c = 201
  · simp [h]
    norm_num
  · simp [h]

theorem coefficient_identity (i k : Fin 6) (c : Fin 293) :
    hodgeCoefficient LiteralP13HodgeReplay.productClassIndex
        LiteralP13HodgeData.boundaryCoefficient
        LiteralP13HodgeData.adjointCoboundaryCoefficient i k c =
      scalarCoefficient 201 (1 / 250) i k c +
        gramCoefficient LiteralP13HodgeReplay.productClassIndex
          LiteralP13HodgeData.qCoefficient i k c +
        residualCoefficient i k c := by
  rw [hodgeCoefficient_eq_direct, gramCoefficient_eq_direct,
    scalarCoefficient_eq_direct]
  unfold residualCoefficient residualNumerator
  push_cast
  ring

/-- The first 288 coefficient classes, partitioned into 36 exact blocks. -/
def initialChunk (i k : Fin 6) (j : Fin 36) : ℕ :=
  ∑ u : Fin 8,
    (residualNumerator i k
      (Fin.castAdd 5 (finProdFinEquiv (j, u)))).natAbs

/-- The final five coefficient classes. -/
def finalChunk (i k : Fin 6) : ℕ :=
  ∑ u : Fin 5,
    (residualNumerator i k (Fin.natAdd 288 u)).natAbs

theorem sum_fin9_explicit {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ u, f u =
      (((((((f 0 + f 1) + f 2) + f 3) + f 4) + f 5) + f 6) + f 7) + f 8 := by
  rw [Fin.sum_univ_add (a := 8) (b := 1), Fin.sum_univ_eight,
    Fin.sum_univ_one]
  simp

/-- Four bounded subtotals of nine initial chunks each.  This second level of
partitioning keeps the final kernel arithmetic within the ordinary elaborator
budget without changing or duplicating any certificate coefficient. -/
def initialPart (i k : Fin 6) (p : Fin 4) : ℕ :=
  ∑ u : Fin 9, initialChunk i k (finProdFinEquiv (p, u))

/-- Part 2, offset 7 is the exceptional identity-containing residual chunk. -/
@[simp] theorem part2Offset7_eq_chunk25 :
    finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) = (25 : Fin 36) := by
  decide +kernel

private theorem sum_fin36_parts {M : Type*} [AddCommMonoid M]
    (f : Fin 36 → M) :
    ∑ j, f j = ∑ p : Fin 4, ∑ u : Fin 9, f (finProdFinEquiv (p, u)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv
    (fun x : Fin 4 × Fin 9 ↦ f (finProdFinEquiv x)) f (fun _ ↦ rfl)).symm

theorem sum_initialChunk_eq_parts (i k : Fin 6) :
    ∑ j : Fin 36, initialChunk i k j = ∑ p : Fin 4, initialPart i k p := by
  unfold initialPart
  exact sum_fin36_parts _

private theorem sum_fin288_blocks {M : Type*} [AddCommMonoid M]
    (f : Fin 288 → M) :
    ∑ c, f c = ∑ j : Fin 36, ∑ u : Fin 8, f (finProdFinEquiv (j, u)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv
    (fun x : Fin 36 × Fin 8 ↦ f (finProdFinEquiv x)) f (fun _ ↦ rfl)).symm

/-- The block decomposition is exhaustive and disjoint by finite equivalence. -/
theorem sum_natAbs_eq_chunks (i k : Fin 6) :
    ∑ c : Fin 293, (residualNumerator i k c).natAbs =
      (∑ j : Fin 36, initialChunk i k j) + finalChunk i k := by
  rw [Fin.sum_univ_add (a := 288) (b := 5)]
  refine congrArg₂ (fun a b : ℕ ↦ a + b) ?_ ?_
  · unfold initialChunk
    exact sum_fin288_blocks _
  · rfl

/-- The same exhaustive partition, grouped into four bounded subtotals. -/
theorem sum_natAbs_eq_parts (i k : Fin 6) :
    ∑ c : Fin 293, (residualNumerator i k c).natAbs =
      (∑ p : Fin 4, initialPart i k p) + finalChunk i k := by
  rw [sum_natAbs_eq_chunks, sum_initialChunk_eq_parts]

theorem abs_residualCoefficient (i k : Fin 6) (c : Fin 293) :
    |residualCoefficient i k c| =
      ((residualNumerator i k c).natAbs : ℚ) / 10000000000000000 := by
  unfold residualCoefficient
  rw [abs_div]
  norm_num

end
end LiteralP13HodgeCertificate
end GroupApproximation
