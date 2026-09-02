import GroupApproximation.GGT.HullSCLemma49LongArc

/-!
# Scaled repeated blocks on a Lemma 4.9 power arc

Osin's long-arc case chooses two equal subwords of the periodic outer
boundary, separated by a macroscopic interval.  The fixed long-period proof
uses blocks of length `|arc|/100`.  For a power-side quasi-geodesic constant
`M`, the same argument needs smaller blocks, and later takes the divisor to be
`100*(M+1)`.

This file proves the finite-word construction for every divisor at least six.
The first period multiple after `blockLength + |arc|/4` is used exactly as in
Hull's invocation of Osin Lemma 6.3.  The divisor bound leaves enough room for
the two blocks and the quarter-length middle interval.
-/

namespace GroupApproximation
namespace HullSC

universe u

/-! ## Arithmetic placement at an arbitrary divisor -/

/-- The first period multiple after `total/divisor + total/4` leaves room for
a second block, provided `divisor ≥ 6` and the period occupies at most three
quarters of the total word. -/
theorem exists_scaled_periodic_block_offset
    {period total divisor : ℕ} (hperiodPos : 0 < period)
    (hdivisor : 6 ≤ divisor) (hlong : 4 * period ≤ 3 * total) :
    ∃ offset : ℕ,
      period ∣ offset ∧
      total / divisor ≤ offset ∧
      total / 4 ≤ offset - total / divisor ∧
      offset + total / divisor ≤ total := by
  let blockLength := total / divisor
  let lower := blockLength + total / 4
  have hblockBudget : divisor * blockLength ≤ total := by
    dsimp [blockLength]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self total divisor
  have hsixBlock : 6 * blockLength ≤ total := by
    have hmul := Nat.mul_le_mul_right blockLength hdivisor
    rw [Nat.mul_comm divisor blockLength] at hblockBudget
    exact le_trans hmul hblockBudget
  have hquarterBudget : 4 * (total / 4) ≤ total := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self total 4
  by_cases hlower : lower ≤ period
  · refine ⟨period, dvd_rfl, ?_, ?_, ?_⟩
    · dsimp [lower] at hlower
      omega
    · dsimp [lower] at hlower
      omega
    · omega
  · have hperiodLower : period < lower := by omega
    let quotient := lower / period
    let offset := (quotient + 1) * period
    have hmod : lower % period < period := Nat.mod_lt _ hperiodPos
    have hdivision : period * quotient + lower % period = lower := by
      simpa [quotient] using Nat.div_add_mod lower period
    have hoffsetForm : offset = period * quotient + period := by
      dsimp only [offset]
      rw [Nat.add_mul, one_mul, Nat.mul_comm quotient period]
    have hlowerOffset : lower ≤ offset := by omega
    have hoffsetUpper : offset ≤ lower + period := by omega
    have htwoLower : offset ≤ 2 * lower := by omega
    have hroom : 2 * lower + blockLength ≤ total := by
      dsimp [lower]
      omega
    refine ⟨offset, ?_, ?_, ?_, ?_⟩
    · exact ⟨quotient + 1, by simp [offset, Nat.mul_comm]⟩
    · dsimp [lower] at hlowerOffset
      omega
    · dsimp [lower] at hlowerOffset
      omega
    · omega

/-! ## Literal scaled repeated-block data -/

/-- Two equal periodic blocks of relative size `1/divisor`, with at least a
quarter of the selected arc between them. -/
structure Lemma49ScaledRepeatedBoundaryBlocks
    (Alpha : Type u) (arc : List Alpha) (divisor : ℕ) where
  block : List Alpha
  middle : List Alpha
  tail : List Alpha
  decomposition : arc = block ++ middle ++ block ++ tail
  block_length : block.length = arc.length / divisor
  middle_long : arc.length / 4 ≤ middle.length

/-- A long periodic word has scaled repeated-block data for every divisor at
least six. -/
theorem exists_scaledRepeatedBoundaryBlocks_of_hasPeriod
    {Alpha : Type u} {arc : List Alpha} {period divisor : ℕ}
    (hperiodPos : 0 < period) (hdivisor : 6 ≤ divisor)
    (hperiod : List.HasPeriod arc period)
    (hlong : 4 * period ≤ 3 * arc.length) :
    Nonempty (Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) := by
  obtain ⟨offset, hoffsetPeriod, hblockOffset, hgap, hfit⟩ :=
    exists_scaled_periodic_block_offset hperiodPos hdivisor hlong
  let blockLength := arc.length / divisor
  let block := arc.take blockLength
  let middle := (arc.drop blockLength).take (offset - blockLength)
  let second := (arc.drop offset).take blockLength
  let tail := arc.drop (offset + blockLength)
  have hblockLength : block.length = blockLength := by
    dsimp [block]
    rw [List.length_take]
    omega
  have hmiddleLength : middle.length = offset - blockLength := by
    dsimp [middle]
    rw [List.length_take, List.length_drop]
    omega
  have hsecond : second = block := by
    dsimp [second, block]
    exact (take_eq_drop_take_of_hasPeriod_of_dvd hperiod
      hoffsetPeriod hfit).symm
  have htakeOffset : arc.take offset = block ++ middle := by
    dsimp [block, middle]
    rw [← List.take_add]
    congr 1
    omega
  have htakeSecond : arc.take (offset + blockLength) =
      arc.take offset ++ second := by
    dsimp [second]
    rw [← List.take_add]
  have hdecomposition : arc = block ++ middle ++ block ++ tail := by
    calc
      arc = arc.take (offset + blockLength) ++
          arc.drop (offset + blockLength) :=
        (List.take_append_drop (offset + blockLength) arc).symm
      _ = (arc.take offset ++ second) ++ tail := by
        rw [htakeSecond]
      _ = (block ++ middle ++ block) ++ tail := by
        rw [htakeOffset, hsecond]
      _ = block ++ middle ++ block ++ tail := by
        simp only [List.append_assoc]
  exact ⟨{
    block := block
    middle := middle
    tail := tail
    decomposition := hdecomposition
    block_length := by simpa [blockLength] using hblockLength
    middle_long := by rw [hmiddleLength]; exact hgap }⟩

/-! ## Application to a power-boundary factor -/

/-- Every long factor of a positive boundary power has scaled repeated-block
data. -/
theorem exists_scaledRepeatedBoundaryBlocks_of_lemma49PowerArc
    {Alpha : Type u} {word arc : List Alpha} {n divisor : ℕ}
    (hn : 0 < n) (harc : arc <:+: lemma49BoundaryPower word n)
    (hperiodPos : 0 < word.length) (hdivisor : 6 ≤ divisor)
    (hlong : 4 * word.length ≤ 3 * arc.length) :
    Nonempty (Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) := by
  have hperiodPower := hasPeriod_lemma49BoundaryPower word hn
  have hperiodArc : List.HasPeriod arc word.length :=
    hperiodPower.infix harc
  exact exists_scaledRepeatedBoundaryBlocks_of_hasPeriod hperiodPos hdivisor
    hperiodArc hlong

/-! ## Basic endpoint bookkeeping -/

/-- Length bookkeeping for a scaled repeated-block decomposition. -/
theorem Lemma49ScaledRepeatedBoundaryBlocks.length_eq
    {Alpha : Type u} {arc : List Alpha} {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) :
    arc.length = 2 * B.block.length + B.middle.length + B.tail.length := by
  have h := congrArg List.length B.decomposition
  simp only [List.length_append] at h
  omega

theorem Lemma49ScaledRepeatedBoundaryBlocks.firstEnd_le
    {Alpha : Type u} {arc : List Alpha} {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) :
    B.block.length ≤ arc.length := by
  have h := B.length_eq
  omega

theorem Lemma49ScaledRepeatedBoundaryBlocks.secondStart_le
    {Alpha : Type u} {arc : List Alpha} {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) :
    B.block.length + B.middle.length ≤ arc.length := by
  have h := B.length_eq
  omega

theorem Lemma49ScaledRepeatedBoundaryBlocks.secondEnd_le
    {Alpha : Type u} {arc : List Alpha} {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor) :
    B.block.length + B.middle.length + B.block.length ≤ arc.length := by
  have h := B.length_eq
  omega

/-! ## Model check -/

/-- A constant word gives nonempty scaled data at a divisor different from
the fixed long-period value. -/
theorem scaledRepeatedBoundaryBlocks_model {Alpha : Type u} (a : Alpha) :
    Nonempty (Lemma49ScaledRepeatedBoundaryBlocks Alpha
      (List.replicate 1200 a) 12) := by
  have hperiod : List.HasPeriod (List.replicate 1200 a) 1 := by
    rw [List.hasPeriod_iff_forall_getElem?_mod]
    intro i hi
    have hi1200 : i < 1200 := by
      simpa only [List.length_replicate] using hi
    have hmod : i % 1 < 1200 := by omega
    rw [List.getElem?_replicate_of_lt hi1200,
      List.getElem?_replicate_of_lt hmod]
  apply exists_scaledRepeatedBoundaryBlocks_of_hasPeriod (period := 1)
    (divisor := 12) (by omega) (by omega) hperiod
  rw [List.length_replicate]
  norm_num

end HullSC
end GroupApproximation
