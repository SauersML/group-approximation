import GroupApproximation.GGT.SystolicDiscZipFold
import GroupApproximation.GGT.SystolicDiscMovesAdapter
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Zipping a boundary backtrack (HC3(d))

A triangulated disc whose boundary walk backtracks, `p ++ u :: v :: u :: q`, gives a disc with
boundary `p ++ u :: q`, unless that walk is the constant walk `[u]`.  On a cycle disc let
`du dv` be the exterior darts of the backtrack and `p` the exterior dart before `du`.  When the
corners before `du` and after `dv` lie at different vertices the pair folds
(`CycleDisc.zip_fold`); otherwise the loop `du dv` pinches off (`ZipPinchStatement`).

* `CycleDisc.boundary_eq_take`: the boundary walk closes up at its first label.
* `CycleDisc.zip_spur`: the backtrack of a cycle disc zips, given the pinch case.
* `zipSpurStatement_of_zipPinch`: HC3(d) from the pinch case.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- The first entry of a nonempty list, as a list. -/
theorem singleton_head_eq_take {α β : Type*} (f : α → β) :
    ∀ (l : List α) (h : l ≠ []), [f (l.head h)] = (l.map f).take 1
  | [], h => (h rfl).elim
  | _ :: _, _ => rfl

namespace CycleDisc

/-- The boundary walk closes up at its first label. -/
theorem boundary_eq_take (D : CycleDisc X) :
    D.boundary = D.cyc.map D.lab ++ (D.cyc.map D.lab).take 1 :=
  congrArg (D.cyc.map D.lab ++ ·) (singleton_head_eq_take D.lab D.cyc D.isFaceCycle.ne_nil)

theorem nonempty_disc (D : CycleDisc X) :
    Nonempty (TriangulatedDisc X (D.cyc.map D.lab ++ (D.cyc.map D.lab).take 1)) := by
  rw [← D.boundary_eq_take]
  exact ⟨D.toTriangulatedDisc⟩

/-- **HC3(d) on a cycle disc**, given the pinch case: the exterior walk
`s ++ du :: dv :: t`, read `u v u` at the backtrack, becomes `s ++ t`. -/
theorem zip_spur (D : CycleDisc X) (hpinch : ZipPinchStatement X) {s t : List D.map.Dart}
    {du dv : D.map.Dart} (hcyc : D.cyc = s ++ du :: dv :: t)
    (hlab : D.lab (D.map.facePerm dv) = D.lab du) (hst : s ++ t ≠ []) :
    ∃ D' : CycleDisc X, D'.cyc.map D'.lab = s.map D.lab ++ t.map D.lab := by
  obtain ⟨p, hprev⟩ := Equiv.surjective D.map.facePerm du
  by_cases h : D.map.sigma.SameCycle (D.map.alpha p) (D.map.alpha dv)
  · exact hpinch D s t p du dv hcyc hprev hlab hst h
  · exact D.zip_fold hcyc hprev hlab hst h

end CycleDisc

/-- **HC3(d)**, zipping a boundary backtrack, from its pinch case. -/
theorem zipSpurStatement_of_zipPinch (hpinch : ZipPinchStatement X) : ZipSpurStatement X := by
  intro p q u v T
  obtain ⟨D, hD⟩ := CycleDisc.exists_of_triangulatedDisc T
  have h : D.cyc.map D.lab ++ [D.lab (D.cyc.head D.isFaceCycle.ne_nil)] =
      p ++ u :: v :: u :: q := hD
  have hz : (D.cyc.map D.lab).take 1 = [D.lab (D.cyc.head D.isFaceCycle.ne_nil)] :=
    (singleton_head_eq_take D.lab D.cyc D.isFaceCycle.ne_nil).symm
  obtain ⟨z, hz0⟩ : ∃ z, D.lab (D.cyc.head D.isFaceCycle.ne_nil) = z := ⟨_, rfl⟩
  rw [hz0] at h hz
  rcases split_boundary D.lab z u p (v :: u :: q) D.cyc h with
    ⟨s, b, t, hcyc, rfl, rfl, hq⟩ | ⟨_, _, hq⟩
  · have hR : D.map.IsFaceCycle (b :: (t ++ s)) := by
      have hr := D.isFaceCycle.rotate s.length
      rw [hcyc, List.rotate_append_length_eq] at hr
      exact hr
    rw [hcyc] at hz
    rcases t with _ | ⟨c, _ | ⟨c', t⟩⟩
    · simp at hq
    · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.cons.injEq] at hq
      obtain ⟨rfl, hbz, rfl⟩ := hq
      rcases s with _ | ⟨x, s⟩
      · exact Or.inr rfl
      · have hnext : D.map.facePerm c = x :=
          (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hR.chain).2).1
        have hx : D.lab x = z := by simpa using hz
        subst hx
        obtain ⟨D', hD'⟩ := D.zip_spur hpinch hcyc (by rw [hnext, hbz]) (by simp)
        refine Or.inl ?_
        have e : (x :: s).map D.lab ++ [D.lab b] =
            D'.cyc.map D'.lab ++ (D'.cyc.map D'.lab).take 1 := by
          rw [hD']
          simp [hbz]
        rw [e]
        exact D'.nonempty_disc
    · simp only [List.map_cons, List.cons_append, List.cons.injEq] at hq
      obtain ⟨rfl, hbc, rfl⟩ := hq
      have hnext : D.map.facePerm c = c' :=
        (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hR.chain).2).1
      obtain ⟨D', hD'⟩ := D.zip_spur hpinch hcyc (by rw [hnext, hbc]) (by simp)
      refine Or.inl ?_
      have e : s.map D.lab ++ D.lab b :: (t.map D.lab ++ [z]) =
          D'.cyc.map D'.lab ++ (D'.cyc.map D'.lab).take 1 := by
        rw [hD']
        rcases s with _ | ⟨x, s⟩
        · have hbz : D.lab b = z := by simpa using hz
          subst hbz
          simp [hbc]
        · have hx : D.lab x = z := by simpa using hz
          subst hx
          simp [hbc]
      rw [e]
      exact D'.nonempty_disc
  · exact absurd hq (List.cons_ne_nil _ _)

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.singleton_head_eq_take
#audit_axioms GroupApproximation.Systolic.CycleDisc.boundary_eq_take
#audit_axioms GroupApproximation.Systolic.CycleDisc.nonempty_disc
#audit_axioms GroupApproximation.Systolic.CycleDisc.zip_spur
#audit_axioms GroupApproximation.Systolic.zipSpurStatement_of_zipPinch
