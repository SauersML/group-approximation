import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoBruhat
import GroupApproximation.Meta.AxiomGuard

/-!
# Elements of `St_I(𝔽₂)` acting trivially lie in the Levi span (lane sk-leavitt-23)

Assume a third index exists and fix `L`.  Take `g` acting trivially on `𝔽₂^I`.

* The Bruhat decomposition `bru_all` puts `g` in `U P` or in `S w_j P`.  The second cell
  moves `e_L`, since `(w_j e_L)_L = 0` (`act_weyl_unitVec`), so `g ∈ U P`.  Then the `U`
  factor fixes `e_L` and is trivial (`eq_one_of_col_fix`), so `g ∈ P`.
* Every element of `P` factors as `s v` with `s ∈ S` and `v ∈ V = rowSpan L`
  (`par_eq_lev_mul_row`).  The row factor `v` is trivial (`eq_one_of_row_zero`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `P = S V`. -/
theorem par_eq_lev_mul_row {L : I} {g : SteinbergGroup I (ZMod 2)} (hg : g ∈ parSpan L) :
    ∃ s ∈ levSpan L, ∃ v ∈ rowSpan L, g = s * v := by
  refine rootSpan_induction (p := fun _ j => j ≠ L)
    (Q := fun g => ∃ s ∈ levSpan L, ∃ v ∈ rowSpan L, g = s * v) ?_ ?_ ?_ hg
  · intro i j h a (hj : j ≠ L)
    by_cases hi : i = L
    · exact ⟨1, Subgroup.one_mem _, x i j h a, x_mem_rootSpan h a hi, (one_mul _).symm⟩
    · exact ⟨x i j h a, x_mem_rootSpan h a ⟨hi, hj⟩, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
  · rintro g k _ _ ⟨s₁, hs₁, v₁, hv₁, rfl⟩ ⟨s₂, hs₂, v₂, hv₂, rfl⟩
    have hc : s₂⁻¹ * v₁ * s₂ ∈ rowSpan L := by
      have h := lev_conj_row (Subgroup.inv_mem _ hs₂) hv₁
      rwa [inv_inv] at h
    exact ⟨s₁ * s₂, Subgroup.mul_mem _ hs₁ hs₂, s₂⁻¹ * v₁ * s₂ * v₂,
      Subgroup.mul_mem _ hc hv₂, by group⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.par_eq_lev_mul_row

/-- `(w_j e_L)_L = 0`. -/
theorem act_weyl_unitVec {j L : I} (hj : j ≠ L) :
    act (weyl j L hj) (unitVec (R := ZMod 2) L) L = 0 := by
  have h1 : act (x j L hj (1 : ZMod 2)) (unitVec L) L = 1 := by
    rw [act_x_apply, if_neg hj.symm, add_zero, unitVec_apply, if_pos rfl]
  have h2 : act (x j L hj (1 : ZMod 2)) (unitVec L) j = 1 := by
    rw [act_x_apply, if_pos rfl, unitVec_apply, unitVec_apply, if_neg hj, if_pos rfl,
      zero_add, mul_one]
  have e : act (weyl j L hj) (unitVec (R := ZMod 2) L) L = 1 + 1 := by
    unfold weyl
    rw [act_mul, act_mul, act_x_apply, if_neg hj.symm, add_zero, act_x_apply, if_pos rfl,
      h1, h2, mul_one]
  exact e.trans (by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.act_weyl_unitVec

/-- An element of `St_I(𝔽₂)` acting trivially lies in `levSpan L`. -/
theorem mem_levSpan_of_act (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) (L : I)
    {g : SteinbergGroup I (ZMod 2)} (hg : ∀ v, act g v = v) : g ∈ levSpan L := by
  have hPe : ∀ p ∈ parSpan L, act p (unitVec (R := ZMod 2) L) = unitVec L := fun p hp =>
    act_eq_self_of_rootSpan (p := fun _ j => j ≠ L)
      (fun _ j (hj : j ≠ L) => by rw [unitVec_apply, if_neg hj]) hp
  have hS : ∀ s ∈ levSpan L, ∀ v : I → ZMod 2, act s v L = v L := fun s hs v =>
    act_apply_of_rootSpan (p := fun i j => i ≠ L ∧ j ≠ L) (k := L)
      (fun _ _ (hq : _ ∧ _) => hq.1) hs v
  have hP : g ∈ parSpan L := by
    rcases bru_all hthird L g with ⟨u, hu, p, hp, rfl⟩ | ⟨j, hj, s, hs, p, hp, rfl⟩
    · have e := hg (unitVec L)
      rw [act_mul, hPe p hp] at e
      rw [eq_one_of_col_fix L hu e, one_mul]
      exact hp
    · exfalso
      have e := congrFun (hg (unitVec L)) L
      rw [act_mul, hPe p hp, act_mul, hS s hs, act_weyl_unitVec hj, unitVec_apply,
        if_pos rfl] at e
      exact absurd e (by decide)
  obtain ⟨s, hs, v, hv, rfl⟩ := par_eq_lev_mul_row hP
  have hv1 : v = 1 := by
    refine eq_one_of_row_zero L hv ?_
    intro k hk
    have e := congrFun (hg (unitVec k)) L
    rw [act_mul, hS s hs, unitVec_apply, if_neg hk.symm] at e
    exact e
  rw [hv1, mul_one]
  exact hs

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.mem_levSpan_of_act

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
