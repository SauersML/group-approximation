import GroupApproximation.Kazhdan.KazhdanImprovement

/-!
# Singleton-core rounding from two coarea inequalities

`KazhdanImprovement.repairRelation_isEpsilonGood_of_boundary` rounds a relation
with small diagonal boundary to a permutation with small commutation defect.
Its proof applies the median-one `ℓ¹` Poincaré inequality to exactly two
functions: the row multiplicities and the column multiplicities of the
relation.  This file takes those two inequalities as the hypotheses.

The reason is the disjoint union of two expander components.  There the
Poincaré inequality holds only for functions that have median one on each
summand separately, and the row and column multiplicities of a relation close
to a swap graph are functions of that kind.
-/

namespace GroupApproximation
namespace CentralizerNormalizationFiberCoarea

open AlmostAutomorphism
open KazhdanImprovement

variable (Y : FiniteModel)

/-- The two coarea inequalities consumed by singleton-core rounding. -/
structure FiberCoarea (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (h : ℝ) : Prop where
  pos : 0 < h
  rows : h * (rowFiberDeviation Y U : ℝ) ≤ ((relationBoundary Y S U).card : ℝ)
  columns :
    h * (columnFiberDeviation Y U : ℝ) ≤ ((relationBoundary Y S U).card : ℝ)

/-- A global Poincaré inequality at median one supplies both inequalities
when at most half of the rows and at most half of the columns are bad. -/
theorem FiberCoarea.of_poincare {S : Finset (Equiv.Perm Y)}
    {U : Finset (Y × Y)} {h : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hrows : 2 * (badRows Y U).card ≤ Fintype.card Y)
    (hcolumns : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    FiberCoarea Y S U h :=
  ⟨hP.1, rowFiberDeviation_mul_le_boundary Y S U hP hrows,
    columnFiberDeviation_mul_le_boundary Y S U hP hcolumns⟩

/-- The rounded permutation differs from the relation by at most seven times
the boundary, divided by the coarea constant. -/
theorem repairRelation_edits_mul_le_boundary_of_fiberCoarea
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hF : FiberCoarea Y S U h) :
    h * (((permutationGraph Y (repairRelation Y U) \ U).card +
      (U \ permutationGraph Y (repairRelation Y U)).card : ℕ) : ℝ) ≤
        7 * ((relationBoundary Y S U).card : ℝ) := by
  have heditsNat := card_repairRelation_edits_le_deviation Y U
  have hedits :
      (((permutationGraph Y (repairRelation Y U) \ U).card +
        (U \ permutationGraph Y (repairRelation Y U)).card : ℕ) : ℝ) ≤
          3 * (rowFiberDeviation Y U : ℝ) +
            4 * (columnFiberDeviation Y U : ℝ) := by
    exact_mod_cast heditsNat
  have hmul := mul_le_mul_of_nonneg_left hedits hF.pos.le
  have hrow := hF.rows
  have hcolumn := hF.columns
  nlinarith

/-- The commutation defect of the rounded permutation is controlled by the
relation boundary alone. -/
theorem repairRelation_badArcs_mul_le_boundary_of_fiberCoarea
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hF : FiberCoarea Y S U h) :
    h * ((badArcs Y S (repairRelation Y U)).card : ℝ) ≤
      (h + 7 * S.card) * ((relationBoundary Y S U).card : ℝ) := by
  have hbase := card_badArcs_le_relationBoundary_add_edits Y S U
    (repairRelation Y U)
  have hedits := repairRelation_edits_mul_le_boundary_of_fiberCoarea Y S U hF
  have hbaseReal :
      ((badArcs Y S (repairRelation Y U)).card : ℝ) ≤
        ((relationBoundary Y S U).card : ℝ) +
          (S.card : ℝ) *
            (((permutationGraph Y (repairRelation Y U) \ U).card +
              (U \ permutationGraph Y (repairRelation Y U)).card : ℕ) : ℝ) := by
    exact_mod_cast hbase
  have hmul := mul_le_mul_of_nonneg_left hbaseReal hF.pos.le
  have hS : (0 : ℝ) ≤ S.card := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hedits hS
  nlinarith

/-- Singleton-core rounding with the two coarea inequalities as hypotheses. -/
theorem repairRelation_isEpsilonGood_of_fiberCoarea
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h ε : ℝ}
    (hF : FiberCoarea Y S U h)
    (hboundary :
      (h + 7 * S.card) * ((relationBoundary Y S U).card : ℝ) <
        h * (ε * Fintype.card Y)) :
    IsEpsilonGood Y S ε (repairRelation Y U) := by
  have hcontrol :=
    repairRelation_badArcs_mul_le_boundary_of_fiberCoarea Y S U hF
  have hbad :
      ((badArcs Y S (repairRelation Y U)).card : ℝ) < ε * Fintype.card Y :=
    lt_of_mul_lt_mul_left (hcontrol.trans_lt hboundary) hF.pos.le
  refine ⟨hbad, ?_⟩
  rw [card_badArcs_inv]
  exact hbad

end CentralizerNormalizationFiberCoarea
end GroupApproximation
