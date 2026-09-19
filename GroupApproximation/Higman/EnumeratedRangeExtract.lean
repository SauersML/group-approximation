import GroupApproximation.Higman.EnumeratedRangeVerify
import GroupApproximation.Higman.TraceRelationRE

/-!
# Extracting the member carried by an anchored trace

The marker at block zero selects the unique active trace window.  Walking the
counter of any active block to zero shows that its block index is its counter
and that its parameter is the parameter at the origin.  Consequently the
value-track projection of every anchored trace is one member of the enumerated
range.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

private theorem traceRel_at {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) (i : ℤ) :
    traceRel c (trVal g i) (trCnt g i) (trPar g i) (trMrk g i)
      (trVal g (i + 1)) (trCnt g (i + 1)) (trPar g (i + 1)) (trMrk g (i + 1)) := by
  exact (mem_transitionSet_blockPairSet (traceRel c) g).mp hg.1 i

private theorem origin_active {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) : 1 ≤ trPar g 0 ∧ trCnt g 0 = 0 := by
  have hrel := traceRel_at hg 0
  rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
  have hmark : trMrk g 0 = 1 := by
    exact trMrk_zero_of_mem_anchorSet hg.2
  have ha : 1 ≤ trPar g 0 ∧ trCnt g 0 = 0 := by
    by_contra h
    rw [if_neg h] at hm
    omega
  exact ha

private theorem active_nonnegative_counter {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) : ∀ (n : ℕ) (i : ℤ),
      trCnt g i = (n : ℤ) → 1 ≤ trPar g i →
        i = (n : ℤ) ∧ trPar g i = trPar g 0 := by
  intro n
  induction n with
  | zero =>
      intro i hcnt hactive
      have hrel := traceRel_at hg i
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hmark : trMrk g i = 1 := by
        rw [hm, if_pos ⟨hactive, by simpa using hcnt⟩]
      have hi : i = 0 := by
        by_contra hne
        have hoff := trMrk_off_zero_of_mem_anchorSet hg.2 i hne
        omega
      subst i
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro i hcnt hactive
      have hrel := traceRel_at hg (i - 1)
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hnextPar : trPar g ((i - 1) + 1) = trPar g i := by congr 1; omega
      have hnextCnt : trCnt g ((i - 1) + 1) = trCnt g i := by congr 1; omega
      have hprevActive : 1 ≤ trPar g (i - 1) := by
        have hnonneg := hp
        by_contra hnot
        have hzero : trPar g (i - 1) = 0 := by omega
        have hlo := hstart hzero (by simpa [hnextPar] using hactive)
        have hlo0 := loIdx_nonpos c (parIdx (trPar g i))
        rw [hnextPar, hnextCnt, hcnt] at hlo
        omega
      have hs := hstep hprevActive (by simpa [hnextPar] using hactive)
      have hprevPar : trPar g (i - 1) = trPar g i := by
        simpa [hnextPar] using hs.1.symm
      have hprevCnt : trCnt g (i - 1) = (n : ℤ) := by
        rw [hnextCnt, hcnt] at hs
        omega
      rcases ih (i - 1) hprevCnt hprevActive with ⟨hi, hpar⟩
      constructor
      · omega
      · exact hprevPar.symm.trans hpar

private theorem active_negative_counter {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) : ∀ (n : ℕ) (i : ℤ),
      trCnt g i = Int.negSucc n → 1 ≤ trPar g i →
        i = Int.negSucc n ∧ trPar g i = trPar g 0 := by
  intro n
  induction n with
  | zero =>
      intro i hcnt hactive
      have hrel := traceRel_at hg i
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hnextActive : 1 ≤ trPar g (i + 1) := by
        by_contra hnot
        have hzero : trPar g (i + 1) = 0 := by omega
        have hhi := hend hactive hzero
        have hhi0 := hiIdx_nonneg c (parIdx (trPar g i))
        omega
      have hs := hstep hactive hnextActive
      have hnextCnt : trCnt g (i + 1) = 0 := by omega
      rcases active_nonnegative_counter hg 0 (i + 1) hnextCnt hnextActive with ⟨hi, hpar⟩
      constructor
      · omega
      · exact hs.1.symm.trans hpar
  | succ n ih =>
      intro i hcnt hactive
      have hrel := traceRel_at hg i
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hnextActive : 1 ≤ trPar g (i + 1) := by
        by_contra hnot
        have hzero : trPar g (i + 1) = 0 := by omega
        have hhi := hend hactive hzero
        have hhi0 := hiIdx_nonneg c (parIdx (trPar g i))
        omega
      have hs := hstep hactive hnextActive
      have hnextCnt : trCnt g (i + 1) = Int.negSucc n := by omega
      rcases ih (i + 1) hnextCnt hnextActive with ⟨hi, hpar⟩
      constructor
      · omega
      · exact hs.1.symm.trans hpar

private theorem active_block_data {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) {i : ℤ} (hactive : 1 ≤ trPar g i) :
    trCnt g i = i ∧ trPar g i = trPar g 0 := by
  cases hcnt : trCnt g i with
  | ofNat n =>
      rcases active_nonnegative_counter hg n i hcnt hactive with ⟨hi, hp⟩
      exact ⟨hi.symm, hp⟩
  | negSucc n =>
      rcases active_negative_counter hg n i hcnt hactive with ⟨hi, hp⟩
      exact ⟨hi.symm, hp⟩

private theorem origin_window_data {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) : ∀ i : ℤ,
      loIdx c (parIdx (trPar g 0)) ≤ i →
      i ≤ hiIdx c (parIdx (trPar g 0)) →
      trPar g i = trPar g 0 ∧ trCnt g i = i := by
  intro i
  induction i using Int.induction_on with
  | zero =>
      intro hlo hhi
      exact ⟨rfl, (origin_active hg).2⟩
  | succ n ih =>
      intro hlo hhi
      have hloPrev : loIdx c (parIdx (trPar g 0)) ≤ (n : ℤ) := by
        exact (loIdx_nonpos c _).trans (Int.natCast_nonneg n)
      have hhiPrev : (n : ℤ) ≤ hiIdx c (parIdx (trPar g 0)) := by omega
      rcases ih hloPrev hhiPrev with ⟨hpar, hcnt⟩
      have hrel := traceRel_at hg (n : ℤ)
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hactive : 1 ≤ trPar g (n : ℤ) := by
        rw [hpar]
        exact (origin_active hg).1
      have hnextActive : 1 ≤ trPar g ((n : ℤ) + 1) := by
        by_contra hnot
        have hzero : trPar g ((n : ℤ) + 1) = 0 := by omega
        have hend' := hend hactive hzero
        rw [hcnt, hpar] at hend'
        omega
      have hs := hstep hactive hnextActive
      exact ⟨hs.1.trans hpar, by rw [hs.2, hcnt]⟩
  | pred n ih =>
      intro hlo hhi
      have hloNext : loIdx c (parIdx (trPar g 0)) ≤ -(n : ℤ) := by omega
      have hhiNext : -(n : ℤ) ≤ hiIdx c (parIdx (trPar g 0)) := by
        exact (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg n)).trans (hiIdx_nonneg c _)
      rcases ih hloNext hhiNext with ⟨hparNext, hcntNext⟩
      have hrel := traceRel_at hg (-(n : ℤ) - 1)
      rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
      have hnextIndex : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      have hnextActive : 1 ≤ trPar g (-(n : ℤ) - 1 + 1) := by
        rw [hnextIndex, hparNext]
        exact (origin_active hg).1
      have hcurrentActive : 1 ≤ trPar g (-(n : ℤ) - 1) := by
        by_contra hnot
        have hzero : trPar g (-(n : ℤ) - 1) = 0 := by omega
        have hstart' := hstart hzero hnextActive
        rw [hnextIndex, hcntNext, hparNext] at hstart'
        omega
      have hs := hstep hcurrentActive hnextActive
      constructor
      · rw [hnextIndex, hparNext] at hs
        exact hs.1.symm
      · rw [hnextIndex, hcntNext] at hs
        omega

/-- Every anchored trace projects to the member selected by the parameter at
the origin. -/
theorem trace_projection_eq_origin_member {c : ℕ → List (ℤ × ℤ)} {g : E}
    (hg : g ∈ traceSet c) (i : ℤ) :
    g (4 * i) = gseq c (parIdx (trPar g 0)) i := by
  have hrel := traceRel_at hg i
  rcases hrel with ⟨hp, hp', hm, hm', hz, hz', hv, hv', hstep, hend, hstart⟩
  by_cases hactive : 1 ≤ trPar g i
  · rcases active_block_data hg hactive with ⟨hcnt, hpar⟩
    have hval := hv hactive
    rw [hcnt, hpar] at hval
    exact hval.2.2
  · have hzero : trPar g i = 0 := by omega
    have hvalzero := (hz hzero).1
    have horigin := origin_active hg
    have hzeroMember : gseq c (parIdx (trPar g 0)) i = 0 := by
      by_cases hlo : i < loIdx c (parIdx (trPar g 0))
      · exact gseq_eq_zero_of_lt c _ hlo
      · by_cases hhi : hiIdx c (parIdx (trPar g 0)) < i
        · exact gseq_eq_zero_of_gt c _ hhi
        · exfalso
          have hinside : loIdx c (parIdx (trPar g 0)) ≤ i ∧
              i ≤ hiIdx c (parIdx (trPar g 0)) := by omega
          have hdata := origin_window_data hg i hinside.1 hinside.2
          rw [hdata.1] at hzero
          exact (not_le_of_gt (by omega : 0 < trPar g 0)) hzero.le
    exact hvalzero.trans hzeroMember.symm

/-- The value-track projections of the anchored traces are exactly the range
of the coded enumeration. -/
theorem traceSet_projection_iff_range (c : ℕ → List (ℤ × ℤ)) (f : E) :
    (∃ g ∈ traceSet c, ∀ i : ℤ, f i = g (4 * i)) ↔
      f ∈ {g : E | ∃ r : ℕ, seqOfList (c r) = g} := by
  constructor
  · rintro ⟨g, hg, hproj⟩
    refine ⟨parIdx (trPar g 0), ?_⟩
    change gseq c (parIdx (trPar g 0)) = f
    ext i
    rw [hproj i]
    exact (trace_projection_eq_origin_member hg i).symm
  · rintro ⟨r, rfl⟩
    refine ⟨traceOf c r, traceOf_mem_traceSet c r, ?_⟩
    intro i
    exact traceOf_projection c r i

end Seq

/-- The trace construction reduces the enumerated-range input to precisely the
bounded-window arithmetic input. -/
theorem enumeratedRangeGenerated_of_boundedWindowRE (h : BoundedWindowRE) :
    EnumeratedRangeGenerated where
  range c hc :=
    Seq.higmanGenerated_range_of_projection_of_computable h c hc
      (Seq.traceSet_projection_iff_range c)

end Higman
end GroupApproximation
