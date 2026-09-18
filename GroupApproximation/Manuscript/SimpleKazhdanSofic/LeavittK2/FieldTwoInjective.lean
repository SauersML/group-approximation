import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction
import GroupApproximation.Meta.AxiomGuard

/-!
# The column and row root groups act faithfully (lane sk-leavitt-23)

Fix an index `L`.

* `eq_one_of_col_fix`: an element of the span of the column roots `x_iL` that fixes `e_L`
  is trivial.
* `eq_one_of_row_zero`: take an element `v` of the span of the row roots `x_Lj`.  If
  `(v e_k)_L = 0` for every `k ≠ L`, then `v` is trivial.

Both results come from induction on the set of rows (resp. columns) allowed.  In the
inductive step one root is split off with `exists_split`, and its coefficient is read off
from one coordinate of the action.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

theorem eq_one_of_col_fix_finset (L : I) (T : Finset I) (hLT : L ∉ T) :
    ∀ u ∈ rootSpan (R := R) (fun i j => j = L ∧ i ∈ T),
      act u (unitVec L) = unitVec L → u = 1 := by
  induction T using Finset.induction_on with
  | empty =>
    intro u hu _
    exact rootSpan_induction (Q := fun g => g = 1)
      (fun i _ _ _ hp => absurd hp.2 (Finset.notMem_empty i)) rfl
      (fun g k _ _ h1 h2 => show g * k = 1 by
        rw [show g = 1 from h1, show k = 1 from h2, mul_one]) hu
  | insert b T hbT ih =>
    intro u hu hfix
    have hbL : b ≠ L := fun h => hLT (by rw [← h]; exact Finset.mem_insert_self b T)
    have hLT' : L ∉ T := fun h => hLT (Finset.mem_insert_of_mem h)
    obtain ⟨d, u', hu', rfl⟩ := exists_split (q := fun i j => j = L ∧ i ∈ T) hbL
      (fun i j _ hp => by
        rcases Finset.mem_insert.mp hp.2 with hi | hi
        · exact Or.inl ⟨hi, hp.1⟩
        · exact Or.inr ⟨hp.1, hi⟩)
      (fun i j h a c hq => x_commute_of_ne b L i j hbL h
        (by rw [← hq.1]; exact h.symm) (by rw [hq.1]; exact hbL.symm) c a) hu
    have h1 : act u' (unitVec L) b = unitVec L b :=
      act_apply_of_rootSpan (p := fun i j => j = L ∧ i ∈ T)
        (fun i _ hp hib => hbT (by rw [← hib]; exact hp.2)) hu' _
    have h2 : act u' (unitVec L) L = unitVec L L :=
      act_apply_of_rootSpan (p := fun i j => j = L ∧ i ∈ T)
        (fun i _ hp hiL => hLT' (by rw [← hiL]; exact hp.2)) hu' _
    have hd : d = 0 := by
      have e := congrFun hfix b
      rw [act_mul, act_x_apply, h1, if_pos rfl, h2] at e
      simpa [unitVec_apply, hbL] using e
    subst hd
    simp only [x_zero, one_mul] at hfix ⊢
    exact ih hLT' u' hu' hfix

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.eq_one_of_col_fix_finset

/-- An element of the column root span `⟨x_iL⟩` fixing `e_L` is trivial. -/
theorem eq_one_of_col_fix (L : I) {u : SteinbergGroup I R}
    (hu : u ∈ rootSpan (R := R) (fun _ j => j = L))
    (hfix : act u (unitVec L) = unitVec L) : u = 1 := by
  refine eq_one_of_col_fix_finset L (Finset.univ.erase L) (Finset.notMem_erase L _) u ?_ hfix
  exact rootSpan_mono (p := fun _ j => j = L)
    (fun i j hij hj =>
      ⟨hj, Finset.mem_erase.mpr ⟨by rw [← hj]; exact hij, Finset.mem_univ i⟩⟩) hu

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.eq_one_of_col_fix

theorem eq_one_of_row_zero_finset (L : I) (T : Finset I) (hLT : L ∉ T) :
    ∀ v ∈ rootSpan (R := R) (fun i j => i = L ∧ j ∈ T),
      (∀ k, k ≠ L → act v (unitVec k) L = 0) → v = 1 := by
  induction T using Finset.induction_on with
  | empty =>
    intro v hv _
    exact rootSpan_induction (Q := fun g => g = 1)
      (fun _ j _ _ hp => absurd hp.2 (Finset.notMem_empty j)) rfl
      (fun g k _ _ h1 h2 => show g * k = 1 by
        rw [show g = 1 from h1, show k = 1 from h2, mul_one]) hv
  | insert b T hbT ih =>
    intro v hv hfix
    have hbL : b ≠ L := fun h => hLT (by rw [← h]; exact Finset.mem_insert_self b T)
    have hLT' : L ∉ T := fun h => hLT (Finset.mem_insert_of_mem h)
    obtain ⟨d, v', hv', rfl⟩ := exists_split (q := fun i j => i = L ∧ j ∈ T) hbL.symm
      (fun i j _ hp => by
        rcases Finset.mem_insert.mp hp.2 with hj | hj
        · exact Or.inl ⟨hp.1, hj⟩
        · exact Or.inr ⟨hp.1, hj⟩)
      (fun i j h a c hq => x_commute_of_ne L b i j hbL.symm h
        (by rw [hq.1]; exact hbL) (by rw [← hq.1]; exact h.symm) c a) hv
    have h1 : act v' (unitVec b) = unitVec b :=
      act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ T)
        (fun _ j hp => by
          rw [unitVec_apply, if_neg (show j ≠ b from fun hjb => hbT (by rw [← hjb]; exact hp.2))]) hv'
    have hd : d = 0 := by
      have e := hfix b hbL
      rw [act_mul, h1, act_x_apply, if_pos rfl] at e
      simpa [unitVec_apply, hbL.symm] using e
    subst hd
    simp only [x_zero, one_mul] at hfix ⊢
    exact ih hLT' v' hv' hfix

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.eq_one_of_row_zero_finset

/-- An element `v` of the row root span `⟨x_Lj⟩` with `(v e_k)_L = 0` for all `k ≠ L` is
trivial. -/
theorem eq_one_of_row_zero (L : I) {v : SteinbergGroup I R}
    (hv : v ∈ rootSpan (R := R) (fun i _ => i = L))
    (hfix : ∀ k, k ≠ L → act v (unitVec k) L = 0) : v = 1 := by
  refine eq_one_of_row_zero_finset L (Finset.univ.erase L) (Finset.notMem_erase L _) v ?_ hfix
  exact rootSpan_mono (p := fun i _ => i = L)
    (fun i j hij hi =>
      ⟨hi, Finset.mem_erase.mpr ⟨by rw [← hi]; exact hij.symm, Finset.mem_univ j⟩⟩) hv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.eq_one_of_row_zero

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
