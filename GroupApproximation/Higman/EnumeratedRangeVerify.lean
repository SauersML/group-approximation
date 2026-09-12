import GroupApproximation.Higman.EnumeratedRangeProjection

/-!
# The trace of a member satisfies the transition relation

`Higman.EnumeratedRangeProjection` builds `Seq.traceOf c r` and reads its four
tracks.  This module discharges the constructive half of the projection
identity: that trace satisfies `Seq.traceRel c` at every adjacent pair, so it
lies in `Seq.traceSet c`.

The case table is in the docstring of `Higman.EnumeratedRangeProjection`; this
file is its transcription.  The split is on `a := i ∈ W` and `b := i+1 ∈ W` for
the normalized window `W`, and the two facts that make the boundary cases work
are that `W` is an interval --- so `a ∧ ¬b` forces `i = hiIdx c r` and `¬a ∧ b`
forces `i+1 = loIdx c r` --- and that `W` contains the index `0`, which is what
the clamping in `Seq.loIdx` and `Seq.hiIdx` buys and what the marker clause
spends.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- A member vanishes off its normalized window, in the form the inactive-block
clauses consume. -/
theorem gseq_eq_zero_of_notMem (c : ℕ → List (ℤ × ℤ)) (r : ℕ) {k : ℤ}
    (hk : ¬(loIdx c r ≤ k ∧ k ≤ hiIdx c r)) : gseq c r k = 0 := by
  by_cases h : k < loIdx c r
  · exact gseq_eq_zero_of_lt c r h
  · exact gseq_eq_zero_of_gt c r (by omega)

/-- **The trace of a member satisfies the transition relation.** -/
theorem traceOf_traceRel (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    traceRel c (trVal (traceOf c r) i) (trCnt (traceOf c r) i)
      (trPar (traceOf c r) i) (trMrk (traceOf c r) i)
      (trVal (traceOf c r) (i + 1)) (trCnt (traceOf c r) (i + 1))
      (trPar (traceOf c r) (i + 1)) (trMrk (traceOf c r) (i + 1)) := by
  have hlo : loIdx c r ≤ 0 := loIdx_nonpos c r
  have hhi : 0 ≤ hiIdx c r := hiIdx_nonneg c r
  by_cases hw : i ∈ Finset.Icc (loIdx c r) (hiIdx c r)
  · by_cases hw' : i + 1 ∈ Finset.Icc (loIdx c r) (hiIdx c r)
    · -- both blocks active
      have hwa : loIdx c r ≤ i ∧ i ≤ hiIdx c r := Finset.mem_Icc.mp hw
      have hwa' : loIdx c r ≤ i + 1 ∧ i + 1 ≤ hiIdx c r := Finset.mem_Icc.mp hw'
      simp only [trVal_traceOf, trCnt_traceOf, trPar_traceOf, trMrk_traceOf,
        if_pos hw, if_pos hw']
      unfold traceRel
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro _
        rw [parIdx_natCast_add_one]
        exact ⟨hwa.1, hwa.2, rfl⟩
      · intro _
        rw [parIdx_natCast_add_one]
        exact ⟨hwa'.1, hwa'.2, rfl⟩
      · intro _ _
        exact ⟨rfl, rfl⟩
      · intro _ h
        exfalso
        omega
      · intro h
        exfalso
        omega
    · -- the window ends at this block
      have hwa : loIdx c r ≤ i ∧ i ≤ hiIdx c r := Finset.mem_Icc.mp hw
      have hwa' : ¬(loIdx c r ≤ i + 1 ∧ i + 1 ≤ hiIdx c r) := fun h =>
        hw' (Finset.mem_Icc.mpr h)
      simp only [trVal_traceOf, trCnt_traceOf, trPar_traceOf, trMrk_traceOf,
        if_pos hw, if_neg hw']
      unfold traceRel
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro h
        exfalso
        omega
      · intro _
        exact ⟨gseq_eq_zero_of_notMem c r hwa', rfl⟩
      · intro _
        rw [parIdx_natCast_add_one]
        exact ⟨hwa.1, hwa.2, rfl⟩
      · intro h
        exfalso
        omega
      · intro _ h
        exfalso
        omega
      · intro _ _
        rw [parIdx_natCast_add_one]
        omega
      · intro h
        exfalso
        omega
  · by_cases hw' : i + 1 ∈ Finset.Icc (loIdx c r) (hiIdx c r)
    · -- the window starts at the next block
      have hwa : ¬(loIdx c r ≤ i ∧ i ≤ hiIdx c r) := fun h =>
        hw (Finset.mem_Icc.mpr h)
      have hwa' : loIdx c r ≤ i + 1 ∧ i + 1 ≤ hiIdx c r := Finset.mem_Icc.mp hw'
      simp only [trVal_traceOf, trCnt_traceOf, trPar_traceOf, trMrk_traceOf,
        if_neg hw, if_pos hw']
      unfold traceRel
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro _
        exact ⟨gseq_eq_zero_of_notMem c r hwa, rfl⟩
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro _
        rw [parIdx_natCast_add_one]
        exact ⟨hwa'.1, hwa'.2, rfl⟩
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro _ _
        rw [parIdx_natCast_add_one]
        omega
    · -- both blocks inactive
      have hwa : ¬(loIdx c r ≤ i ∧ i ≤ hiIdx c r) := fun h =>
        hw (Finset.mem_Icc.mpr h)
      have hwa' : ¬(loIdx c r ≤ i + 1 ∧ i + 1 ≤ hiIdx c r) := fun h =>
        hw' (Finset.mem_Icc.mpr h)
      simp only [trVal_traceOf, trCnt_traceOf, trPar_traceOf, trMrk_traceOf,
        if_neg hw, if_neg hw']
      unfold traceRel
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · intro _
        exact ⟨gseq_eq_zero_of_notMem c r hwa, rfl⟩
      · intro _
        exact ⟨gseq_eq_zero_of_notMem c r hwa', rfl⟩
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro h
        exfalso
        omega
      · intro _ h
        exfalso
        omega

/-- **The trace of a member is an anchored trace.** -/
theorem traceOf_mem_traceSet (c : ℕ → List (ℤ × ℤ)) (r : ℕ) :
    traceOf c r ∈ traceSet c := by
  refine ⟨?_, traceOf_mem_anchorSet c r⟩
  rw [mem_transitionSet_blockPairSet]
  exact traceOf_traceRel c r

end Seq
end Higman
end GroupApproximation
