import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-36c: a rotation is a sublist when every step is forward

Lane gl-p07-36c.  List step of the reduction of
`FourPieceWitness.WitnessCurveSublistNondegStatement` (`FourBlockNondegStepStatement.lean`) to
`FourPieceWitness.WitnessCurveSublistStepStatement` (`WitnessCurveSublistStatement.lean`).
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

* `exists_rotate_sublist_of_steps`: `w`, `l` duplicate free, `l ⊆ w`, and every consecutive pair
  `(x, y)` of every rotation of `l` a `StepNext w l x y` pair.  Then some rotation of `l` is a
  sublist of `w`.  Proof: let `y` be the first entry of `w` in `l`, `w = u ++ y :: z`,
  `l = s ++ y :: t`.  The rotation `r = l.rotate |s| = y :: (t ++ s)` is duplicate free, so no
  consecutive pair of `r` ends at `y`; the second disjunct of `StepNext` would make its end the
  first entry of `w` in `l`, which is `y`.  So every pair is forward, and `sublist_of_forward`
  gives `r <+ y :: z <+ w`.
* `exists_rotate_reverse_sublist_of_steps`: the same with every pair read backwards, for
  `(l.rotate n).reverse`.  Apply the first lemma to `l.reverse` (`List.rotate_reverse`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistList

variable {α : Type*}

/-- **A rotation is a sublist when every cyclic step is a `StepNext` step.** -/
theorem exists_rotate_sublist_of_steps {w l : List α} (hw : w.Nodup) (hl : l.Nodup)
    (hsub : ∀ e ∈ l, e ∈ w)
    (hstep : ∀ (n : ℕ) (s t : List α) (x y : α), l.rotate n = s ++ x :: y :: t →
      StepNext w l x y) :
    ∃ n : ℕ, l.rotate n <+ w := by
  by_cases hex : ∃ x ∈ l, x ∈ w
  · obtain ⟨u, y, z, hwu, hyl, hu⟩ := exists_first_entry hex
    obtain ⟨s, t, hst⟩ := List.append_of_mem hyl
    have hrot : l.rotate s.length = y :: (t ++ s) := by
      rw [hst, List.rotate_append_length_eq, List.cons_append]
    have hyz : y :: z <+ w := by
      rw [hwu]
      exact List.sublist_append_right u (y :: z)
    refine ⟨s.length, ?_⟩
    rw [hrot]
    refine (sublist_of_forward (l := t ++ s) hw hwu ?_).trans hyz
    intro s' t' x y' h
    rcases hstep s.length s' t' x y' (hrot.trans h) with hxy | ⟨u', z', hw', hu'⟩
    · exact hxy
    · exfalso
      have hy'l : y' ∈ l := (List.mem_rotate (n := s.length)).mp (by rw [hrot, h]; simp)
      have hyy : y = y' := first_entry_unique (hwu.symm.trans hw') hyl hy'l hu hu'
      rw [← hyy] at h
      have hnd : ([] ++ y :: (t ++ s)).Nodup := by
        rw [List.nil_append, ← hrot]
        exact List.nodup_rotate.mpr hl
      have h2 : [] ++ y :: (t ++ s) = (s' ++ [x]) ++ y :: t' := by
        rw [List.nil_append, h, List.append_assoc, List.singleton_append]
      exact List.append_ne_nil_of_right_ne_nil s' (List.cons_ne_nil x [])
        (append_cons_inj_of_nodup hnd h2).1.symm
  · refine ⟨0, ?_⟩
    have hnil : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => hex ⟨x, hx, hsub x hx⟩
    rw [hnil, List.rotate_zero]
    exact List.nil_sublist w

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistList.exists_rotate_sublist_of_steps

/-- **The backward form**: when every cyclic step read backwards is a `StepNext` step, the
reverse of some rotation of `l` is a sublist of `w`. -/
theorem exists_rotate_reverse_sublist_of_steps {w l : List α} (hw : w.Nodup) (hl : l.Nodup)
    (hsub : ∀ e ∈ l, e ∈ w)
    (hstep : ∀ (n : ℕ) (s t : List α) (x y : α), l.rotate n = s ++ x :: y :: t →
      StepNext w l y x) :
    ∃ n : ℕ, (l.rotate n).reverse <+ w := by
  have hrev : ∀ (n : ℕ) (s t : List α) (x y : α), l.reverse.rotate n = s ++ x :: y :: t →
      StepNext w l.reverse x y := by
    intro n s t x y hr
    rw [List.rotate_reverse] at hr
    have h' : l.rotate (l.length - n % l.length) = t.reverse ++ y :: x :: s.reverse := by
      rw [← List.reverse_reverse (l.rotate (l.length - n % l.length)), hr]
      simp
    exact StepNext.mono (fun e he => List.mem_reverse.mp he)
      (hstep (l.length - n % l.length) t.reverse s.reverse y x h')
  obtain ⟨n, hn⟩ := exists_rotate_sublist_of_steps hw (List.nodup_reverse.mpr hl)
    (fun e he => hsub e (List.mem_reverse.mp he)) hrev
  refine ⟨l.length - n % l.length, ?_⟩
  rw [List.rotate_reverse l n] at hn
  exact hn

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistList.exists_rotate_reverse_sublist_of_steps

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessCurveSublistList
