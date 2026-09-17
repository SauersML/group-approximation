import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Ideal
import GroupApproximation.Meta.AxiomGuard

/-!
# Left multiplication by generators preserves the monomial span

Lane `sk-leavitt-19`, sixth module.

For any Cohn data `C` over an `F_2`-algebra `R`, the `F_2`-span of the monomials
`α β*` (`monomialSpan`) contains `1 = [] []*` (`one_mem_monomialSpan`) and is stable
under left multiplication by the four generators:

* `e_a · α β* = (a α) β*` (`gen_mul_mem_monomialSpan`);
* `e_a* · [] β* = [] (β a)*`, and `e_a* · (d α) β*` is `α β*` if `a = d` and `0`
  otherwise (`gs_mul_mem_monomialSpan`).

If the generators generate `R` as an algebra, this gives the spanning hypothesis
`∀ r, r ∈ C.monomialSpan` used by `mem_unitSpan_of_mem_span_p`.  It is checked for the
concrete `C_2(F_2)` in `Main.lean`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

namespace CohnTwoData

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R] (C : CohnTwoData R)

theorem monomial_mem_monomialSpan (α β : List (Fin 2)) :
    C.word α * C.coword β ∈ C.monomialSpan := by
  rw [monomialSpan]
  exact Submodule.subset_span ⟨(α, β), rfl⟩

theorem one_mem_monomialSpan : (1 : R) ∈ C.monomialSpan := by
  have h := C.monomial_mem_monomialSpan [] []
  rw [word_nil, coword_nil, mul_one] at h
  exact h

theorem gen_mul_mem_monomialSpan (a : Fin 2) {m : R} (hm : m ∈ C.monomialSpan) :
    C.gen a * m ∈ C.monomialSpan := by
  rw [monomialSpan] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨α, β⟩, rfl⟩ := hx
    show C.gen a * (C.word α * C.coword β) ∈ C.monomialSpan
    rw [← mul_assoc, ← word_cons]
    exact C.monomial_mem_monomialSpan (a :: α) β
  | zero =>
    rw [mul_zero]
    exact C.monomialSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact C.monomialSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact C.monomialSpan.smul_mem c hx

theorem gs_mul_mem_monomialSpan (a : Fin 2) {m : R} (hm : m ∈ C.monomialSpan) :
    C.gs a * m ∈ C.monomialSpan := by
  rw [monomialSpan] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨α, β⟩, rfl⟩ := hx
    show C.gs a * (C.word α * C.coword β) ∈ C.monomialSpan
    cases α with
    | nil =>
      have h : C.gs a * (C.word [] * C.coword β) = C.word [] * C.coword (β ++ [a]) := by
        simp only [coword_append, coword_cons, coword_nil, word_nil, one_mul]
      rw [h]
      exact C.monomial_mem_monomialSpan [] (β ++ [a])
    | cons d α =>
      rw [word_cons, ← mul_assoc, ← mul_assoc, gs_mul_gen]
      by_cases had : a = d
      · rw [if_pos had, one_mul]
        exact C.monomial_mem_monomialSpan α β
      · rw [if_neg had, zero_mul, zero_mul]
        exact C.monomialSpan.zero_mem
  | zero =>
    rw [mul_zero]
    exact C.monomialSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact C.monomialSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact C.monomialSpan.smul_mem c hx

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.monomial_mem_monomialSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.one_mem_monomialSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.gen_mul_mem_monomialSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.gs_mul_mem_monomialSpan
