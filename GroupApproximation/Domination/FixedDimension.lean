import GroupApproximation.Domination.Unitary
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Fixed-dimensional domination and dimension escape

This file separates the elementary uniformity argument from the difficult
analytic input of the paper.  The analytic/jet theorem will prove domination
in every fixed dimension for a sofic-radical word.  What is proved here is the
exact consequence of that family of bounds: if global domination nevertheless
fails, one can choose bad representations whose dimensions tend to infinity.

The conclusion is stronger than existence of an unbounded subsequence.  Every
fixed finite range of dimensions is eventually avoided.  No compactness,
curve selection, or representation theory is used in this step.
-/

namespace GroupApproximation

open scoped BigOperators

variable (G : Type*) [Group G]

/-- A character domination inequality restricted to one exact matrix
dimension. -/
def HasFDCharacterDominationInDimension
    (d : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    Fintype.card π.carrier = d →
      π.characterDefect w ≤
        C * (fdUnitaryPowerDefectSystem G).totalDefect R π

/-- One domination constant for all representations of dimension at most
`D`. -/
def HasFDCharacterDominationUpToDimension
    (D : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    Fintype.card π.carrier ≤ D →
      π.characterDefect w ≤
        C * (fdUnitaryPowerDefectSystem G).totalDefect R π

theorem hasFDCharacterDominationInDimension_of_global
    {d : ℕ} {R : Finset G} {w : G}
    (h : HasFDCharacterDomination G R w) :
    HasFDCharacterDominationInDimension G d R w := by
  obtain ⟨C, hC, hdom⟩ := h
  exact ⟨C, hC, fun π _ ↦ hdom π⟩

/-- Finitely many dimension-by-dimension constants combine into one constant
for the entire bounded-dimensional range. -/
theorem hasFDCharacterDominationUpToDimension_of_each
    {D : ℕ} {R : Finset G} {w : G}
    (h : ∀ d ≤ D, HasFDCharacterDominationInDimension G d R w) :
    HasFDCharacterDominationUpToDimension G D R w := by
  classical
  let C : ℕ → ℝ := fun d ↦ if hd : d ≤ D then Classical.choose (h d hd) else 0
  have hC : ∀ d ≤ D, 0 ≤ C d := by
    intro d hd
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (h d hd)).1
  have hdom : ∀ d, (hd : d ≤ D) → ∀ π : FDUnitaryRepresentation G,
      Fintype.card π.carrier = d →
        π.characterDefect w ≤
          C d * (fdUnitaryPowerDefectSystem G).totalDefect R π := by
    intro d hd π hπ
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (h d hd)).2 π hπ
  let Csum : ℝ := ∑ d ∈ Finset.range (D + 1), C d
  refine ⟨Csum, ?_, ?_⟩
  · unfold Csum
    exact Finset.sum_nonneg fun d hd ↦ hC d
      (Nat.le_of_lt_succ (Finset.mem_range.mp hd))
  · intro π hπ
    let d := Fintype.card π.carrier
    have hd : d ≤ D := hπ
    have hdmem : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
    have hCd : C d ≤ Csum := by
      unfold Csum
      exact Finset.single_le_sum
        (fun i hi ↦ hC i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hdmem
    have htotal := (fdUnitaryPowerDefectSystem G).totalDefect_nonneg R π
    exact (hdom d hd π rfl).trans
      (mul_le_mul_of_nonneg_right hCd htotal)

/-- A sequence violates domination at an asymptotically arbitrary linear
scale. -/
def IsFDDominationEscapingSequence
    (R : Finset G) (w : G) (π : ℕ → FDUnitaryRepresentation G) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ N : ℕ, ∀ n ≥ N,
    C * (fdUnitaryPowerDefectSystem G).totalDefect R (π n) <
      (π n).characterDefect w

/-- Failure of a global domination constant supplies a bad representation at
every integer scale. -/
theorem exists_fdDominationEscapingSequence
    {R : Finset G} {w : G}
    (h : ¬ HasFDCharacterDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsFDDominationEscapingSequence G R w π := by
  have hbad : ∀ n : ℕ, ∃ π : FDUnitaryRepresentation G,
      (n : ℝ) * (fdUnitaryPowerDefectSystem G).totalDefect R π <
        π.characterDefect w := by
    intro n
    by_contra hn
    apply h
    refine ⟨n, Nat.cast_nonneg n, ?_⟩
    intro π
    exact le_of_not_gt (not_exists.mp hn π)
  choose π hπ using hbad
  refine ⟨π, ?_⟩
  intro C hC
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, fun n hn ↦ ?_⟩
  have hCn : C ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have htotal := (fdUnitaryPowerDefectSystem G).totalDefect_nonneg R (π n)
  exact (mul_le_mul_of_nonneg_right hCn htotal).trans_lt (hπ n)

/-- **Dimension escape.**  If every fixed dimension has a finite domination
constant while no dimension-independent constant exists, there is a bad
sequence whose dimensions tend to infinity in the literal `atTop` sense.

The forthcoming jet theorem supplies the fixed-dimensional hypothesis from
sofic-radical membership. -/
theorem obstruction_requires_dimensionEscape
    {R : Finset G} {w : G}
    (hfixed : ∀ d, HasFDCharacterDominationInDimension G d R w)
    (hglobal : ¬ HasFDCharacterDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsFDDominationEscapingSequence G R w π ∧
      Filter.Tendsto (fun n ↦ Fintype.card (π n).carrier)
        Filter.atTop Filter.atTop := by
  obtain ⟨π, hπ⟩ := exists_fdDominationEscapingSequence G hglobal
  refine ⟨π, hπ, Filter.tendsto_atTop.2 ?_⟩
  intro D
  have hup : HasFDCharacterDominationUpToDimension G D R w :=
    hasFDCharacterDominationUpToDimension_of_each G
      (fun d _ ↦ hfixed d)
  obtain ⟨C, hC, hdom⟩ := hup
  obtain ⟨N, hN⟩ := hπ C hC
  refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
  by_contra hnot
  have hdim : Fintype.card (π n).carrier ≤ D :=
    Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  exact (not_lt_of_ge (hdom (π n) hdim)) (hN n hn)

end GroupApproximation
