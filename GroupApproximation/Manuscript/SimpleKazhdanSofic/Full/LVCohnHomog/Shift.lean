import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnGraded.Admissible
import GroupApproximation.Meta.AxiomGuard

/-!
# Shifting a potential by a constant (lane sk-lv-05)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii: stable `K₂` of the
Cohn algebra `C = C_2(𝔽₂)` vanishes.  Degree alignment in the homogeneous route uses the fact
that a potential `m` only matters up to an additive constant.

The corner `a ↦ x₀ a y₀` preserves the degree-zero part `C₀`.  On a generator `x_μ y_ν` of `C₀`
it gives `x_{0μ} y_{0ν}`.  It is additive, and it is multiplicative because `y₀ x₀ = 1`.  It is
not unital, but `x₀ y₀ = x_{[0]} y_{[0]}` lies in `C₀`.  Therefore `(p, q)`-admissible implies
`(p + k, q + k)`-admissible, and `skCohnGr_gradedSt m ≤ skCohnGr_gradedSt (m + k)`.

* `skCohnHo_conj_mem_degreeZero`: `c ∈ C₀ → x₀ c y₀ ∈ C₀`.
* `skCohnHo_admissible_add_const`: `(p, q)`-admissible implies `(p + k, q + k)`-admissible.
* `skCohnHo_gradedSt_le_shift`: the shift inclusion of graded Steinberg subgroups.
-/

namespace GroupApproximation.Full.LVCohnHomog

open LVCohnRelK1

noncomputable section

/-- `x₀ (x_μ y_ν) y₀ = x_{0μ} y_{0ν}`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnHo_conj_xw_mul_yw (μ ν : List Bool) :
    cx false * (xw μ * yw ν) * cy false = xw (false :: μ) * yw (false :: ν) := by
  rw [xw_cons, yw_cons]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_conj_xw_mul_yw

/-- **The corner `a ↦ x₀ a y₀` preserves `C₀`.**  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnHo_conj_mem_degreeZero {c : CohnTwoF2}
    (hc : c ∈ LVCohnDegZero.cohnDegreeZero) :
    cx false * c * cy false ∈ LVCohnDegZero.cohnDegreeZero := by
  unfold LVCohnDegZero.cohnDegreeZero at hc
  induction hc using Subring.closure_induction with
  | mem a ha =>
    obtain ⟨μ, ν, h, rfl⟩ := ha
    rw [LVCohnDegZero.cxWord_eq_xw, LVCohnDegZero.cyWord_eq_yw, skCohnHo_conj_xw_mul_yw]
    refine LVCohnDegZero.xw_mul_yw_mem _ _ ?_
    rw [List.length_cons, List.length_cons, h]
  | zero =>
    rw [mul_zero, zero_mul]
    exact zero_mem _
  | one =>
    have h := LVCohnDegZero.xw_mul_yw_mem [false] [false] rfl
    rw [mul_one]
    simpa only [xw_cons, xw_nil, yw_cons, yw_nil, mul_one, one_mul] using h
  | add _ _ _ _ hx hy =>
    rw [mul_add, add_mul]
    exact add_mem hx hy
  | neg _ _ hx =>
    rw [mul_neg, neg_mul]
    exact neg_mem hx
  | mul a b _ _ ha hb =>
    have e : cx false * (a * b) * cy false =
        cx false * a * cy false * (cx false * b * cy false) := by
      calc cx false * (a * b) * cy false
          = cx false * a * (cy false * cx false) * b * cy false := by
            rw [y0_x0, mul_one, mul_assoc (cx false) a b]
        _ = _ := by simp only [mul_assoc]
    rw [e]
    exact mul_mem ha hb

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_conj_mem_degreeZero

/-- `(p, q)`-admissible implies `(p + 1, q + 1)`-admissible.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_admissible_succ {p q : ℕ} {a : CohnTwoF2}
    (ha : LVCohnGraded.skCohnGr_Admissible p q a) :
    LVCohnGraded.skCohnGr_Admissible (p + 1) (q + 1) a := by
  unfold LVCohnGraded.skCohnGr_Admissible at ha ⊢
  have e : cx false ^ (p + 1) * a * cy false ^ (q + 1) =
      cx false * (cx false ^ p * a * cy false ^ q) * cy false := by
    rw [pow_succ' (cx false) p, pow_succ (cy false) q]
    simp only [mul_assoc]
  rw [e]
  exact skCohnHo_conj_mem_degreeZero ha

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_admissible_succ

/-- `(p, q)`-admissible implies `(p + k, q + k)`-admissible.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_admissible_add_const {p q : ℕ} {a : CohnTwoF2}
    (ha : LVCohnGraded.skCohnGr_Admissible p q a) :
    ∀ k : ℕ, LVCohnGraded.skCohnGr_Admissible (p + k) (q + k) a
  | 0 => ha
  | k + 1 => by
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    exact skCohnHo_admissible_succ (skCohnHo_admissible_add_const ha k)

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_admissible_add_const

/-- **Shift invariance**: raising a potential by a constant enlarges the graded Steinberg
subgroup.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnHo_gradedSt_le_shift {n : ℕ} (m : Fin n → ℕ) (k : ℕ) :
    LVCohnGraded.skCohnGr_gradedSt m ≤ LVCohnGraded.skCohnGr_gradedSt (fun i => m i + k) := by
  rw [LVCohnGraded.skCohnGr_gradedSt, Subgroup.closure_le]
  rintro g ⟨i, j, hij, a, ha, rfl⟩
  exact LVCohnGraded.skCohnGr_x_mem_gradedSt (fun i => m i + k) hij
    (skCohnHo_admissible_add_const ha k)

#audit_axioms GroupApproximation.Full.LVCohnHomog.skCohnHo_gradedSt_le_shift

end

end GroupApproximation.Full.LVCohnHomog
