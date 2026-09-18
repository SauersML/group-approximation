import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl element identities over `𝔽₂` (lane sk-leavitt-23)

Put `A = x_jL(1)`, `B = x_Lj(1)` and `w = weyl j L = ABA`.  Assume a third index exists.

* `weyl_conj_corner` together with `w⁻¹ = w` gives `ABABA = B`.  Hence `B w = AB`
  (`row_mul_weyl`) and `A w = w B` (`col_mul_weyl`).
* `w_b` conjugates the column roots `x_iL` (`i ≠ b`) into `levSpan L`
  (`weyl_conj_colExcept`).
* `w_j` conjugates the row roots `x_Lk` (`k ≠ j`) into `parSpan L`
  (`weyl_conj_rowExcept`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem braid_aux {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hk : a * b * a * a * (a * b * a) = b) : a * b * a * b * a = b := by
  calc a * b * a * b * a = a * b * (a * a) * (a * b * a) := by
        rw [ha, mul_one]; simp only [mul_assoc]
    _ = a * b * a * a * (a * b * a) := by simp only [mul_assoc]
    _ = b := hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.braid_aux

theorem weyl_braid_two (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {j L : I} (hj : j ≠ L) :
    x j L hj (1 : ZMod 2) * x L j hj.symm 1 * x j L hj 1 * x L j hj.symm 1 * x j L hj 1 =
      x L j hj.symm 1 := by
  obtain ⟨m, hmj, hmL⟩ := hthird j L
  have hk := weyl_conj_corner two_eq_zero j L m hj hmj hmL (1 : ZMod 2)
  rw [weyl_inv two_eq_zero] at hk
  exact braid_aux (WeylCalc.x_mul_self two_eq_zero j L hj 1) hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.weyl_braid_two

/-- `x_Lj(1) · w_j = x_jL(1) · x_Lj(1)`. -/
theorem row_mul_weyl (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {j L : I} (hj : j ≠ L) :
    x L j hj.symm (1 : ZMod 2) * weyl j L hj = x j L hj 1 * x L j hj.symm 1 := by
  have h1 := weyl_braid_two hthird hj
  have ha := WeylCalc.x_mul_self two_eq_zero j L hj (1 : ZMod 2)
  unfold weyl
  calc x L j hj.symm (1 : ZMod 2) * (x j L hj 1 * x L j hj.symm 1 * x j L hj 1)
      = x j L hj 1 * x j L hj 1 * (x L j hj.symm 1 * (x j L hj 1 * x L j hj.symm 1 *
          x j L hj 1)) := by rw [ha, one_mul]
    _ = x j L hj 1 * (x j L hj (1 : ZMod 2) * x L j hj.symm 1 * x j L hj 1 * x L j hj.symm 1 *
          x j L hj 1) := by simp only [mul_assoc]
    _ = x j L hj 1 * x L j hj.symm 1 := by rw [h1]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.row_mul_weyl

/-- `x_jL(1) · w_j = w_j · x_Lj(1)`. -/
theorem col_mul_weyl (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {j L : I} (hj : j ≠ L) :
    x j L hj (1 : ZMod 2) * weyl j L hj = weyl j L hj * x L j hj.symm 1 := by
  have h1 := weyl_braid_two hthird hj
  have ha := WeylCalc.x_mul_self two_eq_zero j L hj (1 : ZMod 2)
  unfold weyl
  calc x j L hj (1 : ZMod 2) * (x j L hj 1 * x L j hj.symm 1 * x j L hj 1)
      = x L j hj.symm 1 * x j L hj 1 := by
        rw [← mul_assoc, ← mul_assoc, ha, one_mul]
    _ = x j L hj (1 : ZMod 2) * x L j hj.symm 1 * x j L hj 1 * x L j hj.symm 1 * x j L hj 1 *
          x j L hj 1 := by rw [h1]
    _ = x j L hj 1 * x L j hj.symm 1 * x j L hj 1 * x L j hj.symm 1 := by
        rw [mul_assoc _ (x j L hj (1 : ZMod 2)) (x j L hj (1 : ZMod 2)), ha, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.col_mul_weyl

/-- `w_b` conjugates the column roots `x_iL` with `i ≠ b` into `levSpan L`. -/
theorem weyl_conj_colExcept (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {b L : I}
    (hb : b ≠ L) {u : SteinbergGroup I (ZMod 2)}
    (hu : u ∈ rootSpan (R := ZMod 2) (fun i j => j = L ∧ i ≠ b)) :
    weyl b L hb * u * (weyl b L hb)⁻¹ ∈ levSpan L := by
  refine rootSpan_conj_mem ?_ hu
  intro i j h a hp
  have hiL : i ≠ L := by rw [← hp.1]; exact h
  rw [weyl_conj_x_of_third two_eq_zero hb (hthird b L) i j h a]
  refine x_mem_rootSpan _ _ ⟨?_, ?_⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hp.2 hiL]
    exact hiL
  · rw [hp.1, Equiv.swap_apply_right]
    exact hb

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.weyl_conj_colExcept

/-- `w_j` conjugates the row roots `x_Lk` with `k ≠ j` into `parSpan L`. -/
theorem weyl_conj_rowExcept (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {j L : I}
    (hj : j ≠ L) {v : SteinbergGroup I (ZMod 2)}
    (hv : v ∈ rootSpan (R := ZMod 2) (fun i k => i = L ∧ k ≠ j)) :
    weyl j L hj * v * (weyl j L hj)⁻¹ ∈ parSpan L := by
  refine rootSpan_conj_mem ?_ hv
  intro i k h a hp
  have hkL : k ≠ L := by rw [← hp.1]; exact h.symm
  rw [weyl_conj_x_of_third two_eq_zero hj (hthird j L) i k h a]
  refine x_mem_rootSpan _ _ ?_
  show Equiv.swap j L k ≠ L
  rw [Equiv.swap_apply_of_ne_of_ne hp.2 hkL]
  exact hkL

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.weyl_conj_rowExcept

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
