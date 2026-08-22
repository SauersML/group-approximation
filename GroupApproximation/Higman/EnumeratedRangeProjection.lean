import GroupApproximation.Higman.EnumeratedRangeTraceCorrectness

/-!
# The trace of a member, built without division

`Higman.EnumeratedRangeTraceCorrectness` fixes the transition relation
`Seq.traceRel` and bridges `Seq.transitionSet` to the four tracks.  What the
projection identity needs from the constructive side is, for each `r`, an actual
sequence whose tracks are the intended ones.  This module builds it.

## The trap this construction avoids

> Do NOT define the trace by integer division on the coordinate.  `Int.div`
> truncates toward zero and `Int.ediv` floors toward `-∞`; they disagree on
> negative arguments, and this window is genuinely two-sided, so a `x / 4` /
> `x % 4` definition is a silent CORRECTNESS bug on the negative half, not just
> `omega` friction.

The construction below never divides.  Each track is laid down by
`Finsupp.mapDomain` along one of the four injections `i ↦ 4i`, `i ↦ 4i+1`,
`i ↦ 4i+2`, and the marker is the single sequence `Finsupp.single 3 1`.  Reading
a track back is then `Finsupp.mapDomain_apply` at the injection that carries it
and `Finsupp.mapDomain_notin_range` at the other three, and every side condition
is a linear fact about `4k + a` that `omega` settles without ever mentioning
division.

## The four tracks of `Seq.traceOf`

* value --- the member `gseq c r` itself, laid on the coordinates `4i`.  No
  window condition appears: the member already vanishes outside its normalized
  window, by `Seq.gseq_eq_zero_of_lt` and `Seq.gseq_eq_zero_of_gt`;
* counter --- the block index, on `[loIdx c r, hiIdx c r]` and zero off it;
* parameter --- the constant `r + 1` on the same window, so that `0` is free to
  mean inactive;
* marker --- `Finsupp.single 3 1`, a single entry at the coordinate `3`, which is
  the marker slot of block `0`.  The marker needs no window condition either:
  the intended marker is `1` exactly when the block is active and its counter
  reads `0`, and since the normalized window contains the index `0` and the
  counter reads the block index there, that happens at block `0` and nowhere
  else.

`Seq.traceOf_mem_anchorSet` is the last of these observations, discharged.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The three injections -/

theorem four_injective : Function.Injective (fun i : ℤ => 4 * i) := by
  intro x y h
  have h' : (4 : ℤ) * x = 4 * y := h
  omega

theorem four_add_one_injective : Function.Injective (fun i : ℤ => 4 * i + 1) := by
  intro x y h
  have h' : (4 : ℤ) * x + 1 = 4 * y + 1 := h
  omega

theorem four_add_two_injective : Function.Injective (fun i : ℤ => 4 * i + 2) := by
  intro x y h
  have h' : (4 : ℤ) * x + 2 = 4 * y + 2 := h
  omega

/-! ## 2.  The counter and parameter tracks -/

/-- The counter track: the block index on the normalized window, zero off it. -/
noncomputable def cntSeq (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : E :=
  Finsupp.onFinset (Finset.Icc (loIdx c r) (hiIdx c r))
    (fun i => if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then i else 0)
    (by
      intro i hi
      by_contra hcon
      rw [if_neg hcon] at hi
      exact hi rfl)

theorem cntSeq_apply (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    cntSeq c r i = if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then i else 0 := by
  unfold cntSeq
  rw [Finsupp.onFinset_apply]

/-- The parameter track: the constant `r + 1` on the normalized window. -/
noncomputable def parSeq (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : E :=
  Finsupp.onFinset (Finset.Icc (loIdx c r) (hiIdx c r))
    (fun i => if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then (r : ℤ) + 1 else 0)
    (by
      intro i hi
      by_contra hcon
      rw [if_neg hcon] at hi
      exact hi rfl)

theorem parSeq_apply (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    parSeq c r i =
      if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then (r : ℤ) + 1 else 0 := by
  unfold parSeq
  rw [Finsupp.onFinset_apply]

/-! ## 3.  The trace -/

/-- **The trace of the `r`-th member of the enumeration.** -/
noncomputable def traceOf (c : ℕ → List (ℤ × ℤ)) (r : ℕ) : E :=
  Finsupp.mapDomain (fun i : ℤ => 4 * i) (gseq c r)
    + Finsupp.mapDomain (fun i : ℤ => 4 * i + 1) (cntSeq c r)
    + Finsupp.mapDomain (fun i : ℤ => 4 * i + 2) (parSeq c r)
    + Finsupp.single 3 1

theorem traceOf_apply_val (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (k : ℤ) :
    traceOf c r (4 * k) = gseq c r k := by
  unfold traceOf
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply]
  have h1 : Finsupp.mapDomain (fun i : ℤ => 4 * i) (gseq c r) (4 * k) = gseq c r k :=
    Finsupp.mapDomain_apply four_injective (gseq c r) k
  have h2 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 1) (cntSeq c r) (4 * k) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 1 = 4 * k := hi
    omega
  have h3 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 2) (parSeq c r) (4 * k) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 2 = 4 * k := hi
    omega
  have h4 : (Finsupp.single (3 : ℤ) (1 : ℤ)) (4 * k) = 0 := by
    rw [Finsupp.single_apply, if_neg (by omega : ¬((3 : ℤ) = 4 * k))]
  rw [h1, h2, h3, h4]
  simp

theorem traceOf_apply_cnt (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (k : ℤ) :
    traceOf c r (4 * k + 1) = cntSeq c r k := by
  unfold traceOf
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply]
  have h1 : Finsupp.mapDomain (fun i : ℤ => 4 * i) (gseq c r) (4 * k + 1) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i = 4 * k + 1 := hi
    omega
  have h2 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 1) (cntSeq c r) (4 * k + 1)
      = cntSeq c r k :=
    Finsupp.mapDomain_apply four_add_one_injective (cntSeq c r) k
  have h3 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 2) (parSeq c r) (4 * k + 1) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 2 = 4 * k + 1 := hi
    omega
  have h4 : (Finsupp.single (3 : ℤ) (1 : ℤ)) (4 * k + 1) = 0 := by
    rw [Finsupp.single_apply, if_neg (by omega : ¬((3 : ℤ) = 4 * k + 1))]
  rw [h1, h2, h3, h4]
  simp

theorem traceOf_apply_par (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (k : ℤ) :
    traceOf c r (4 * k + 2) = parSeq c r k := by
  unfold traceOf
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply]
  have h1 : Finsupp.mapDomain (fun i : ℤ => 4 * i) (gseq c r) (4 * k + 2) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i = 4 * k + 2 := hi
    omega
  have h2 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 1) (cntSeq c r) (4 * k + 2) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 1 = 4 * k + 2 := hi
    omega
  have h3 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 2) (parSeq c r) (4 * k + 2)
      = parSeq c r k :=
    Finsupp.mapDomain_apply four_add_two_injective (parSeq c r) k
  have h4 : (Finsupp.single (3 : ℤ) (1 : ℤ)) (4 * k + 2) = 0 := by
    rw [Finsupp.single_apply, if_neg (by omega : ¬((3 : ℤ) = 4 * k + 2))]
  rw [h1, h2, h3, h4]
  simp

theorem traceOf_apply_mrk (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (k : ℤ) :
    traceOf c r (4 * k + 3) = if k = 0 then 1 else 0 := by
  unfold traceOf
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply]
  have h1 : Finsupp.mapDomain (fun i : ℤ => 4 * i) (gseq c r) (4 * k + 3) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i = 4 * k + 3 := hi
    omega
  have h2 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 1) (cntSeq c r) (4 * k + 3) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 1 = 4 * k + 3 := hi
    omega
  have h3 : Finsupp.mapDomain (fun i : ℤ => 4 * i + 2) (parSeq c r) (4 * k + 3) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨i, hi⟩
    have hi' : (4 : ℤ) * i + 2 = 4 * k + 3 := hi
    omega
  have h4 : (Finsupp.single (3 : ℤ) (1 : ℤ)) (4 * k + 3) = if k = 0 then 1 else 0 := by
    rw [Finsupp.single_apply]
    by_cases hk : k = 0
    · rw [if_pos (by omega : (3 : ℤ) = 4 * k + 3), if_pos hk]
    · rw [if_neg (by omega : ¬((3 : ℤ) = 4 * k + 3)), if_neg hk]
  rw [h1, h2, h3, h4]
  simp

/-! ## 4.  The four tracks, read back -/

theorem trVal_traceOf (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    trVal (traceOf c r) i = gseq c r i :=
  traceOf_apply_val c r i

theorem trCnt_traceOf (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    trCnt (traceOf c r) i =
      if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then i else 0 := by
  show traceOf c r (4 * i + 1) = _
  rw [traceOf_apply_cnt, cntSeq_apply]

theorem trPar_traceOf (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    trPar (traceOf c r) i =
      if i ∈ Finset.Icc (loIdx c r) (hiIdx c r) then (r : ℤ) + 1 else 0 := by
  show traceOf c r (4 * i + 2) = _
  rw [traceOf_apply_par, parSeq_apply]

theorem trMrk_traceOf (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    trMrk (traceOf c r) i = if i = 0 then 1 else 0 := by
  show traceOf c r (4 * i + 3) = _
  rw [traceOf_apply_mrk]

/-! ## 5.  The trace is anchored, and it projects to its member -/

theorem traceOf_mem_anchorSet (c : ℕ → List (ℤ × ℤ)) (r : ℕ) :
    traceOf c r ∈ anchorSet := by
  refine ⟨?_, ?_⟩
  · show traceOf c r 3 = 1
    have h := traceOf_apply_mrk c r 0
    simpa using h
  · intro i hi
    have h := traceOf_apply_mrk c r i
    rw [if_neg hi] at h
    simpa using h

/-- **The projection of the trace of `r` is the `r`-th member.** -/
theorem traceOf_projection (c : ℕ → List (ℤ × ℤ)) (r : ℕ) (i : ℤ) :
    gseq c r i = traceOf c r (4 * i) :=
  (traceOf_apply_val c r i).symm

end Seq
end Higman
end GroupApproximation
