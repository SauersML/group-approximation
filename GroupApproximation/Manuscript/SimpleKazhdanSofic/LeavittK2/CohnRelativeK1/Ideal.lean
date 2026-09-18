import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Excision
import GroupApproximation.Meta.AxiomGuard

/-!
# The ideal `(p)` is the span of the matrix units

Lane `sk-leavitt-19`, fifth module.

Assume the monomials `α β*` span `R` over `F_2` (true for the Cohn algebra `C_2`,
where they form a basis).  Then the `F_2`-span `M` of the matrix units `α p β*`
is closed under left and right multiplication by `R`
(`mul_mem_unitSpan`, `mul_mem_unitSpan'`), using

* `β* (γ p δ*) ∈ {0} ∪ {γ' p δ*}` (`coword_mul_unit`), and `α (γ p δ*) = (αγ) p δ*`;
* `(γ p δ*) α ∈ {0} ∪ {γ p δ'*}` (`unit_mul_word`), and `(γ p δ*) β* = γ p (βδ)*`.

Hence the two-sided ideal `I = (p)` is contained in `M` (`mem_unitSpan_of_mem_span_p`).
Together with excision (`mem_relativeElementary_of_unitSpan`) this gives the relative
`K_1` statement `GL_ι(R, I) = EL_ι(R, I)` for `#ι ≥ 2` (see `Main.lean`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

namespace CohnTwoData

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R] (C : CohnTwoData R)

theorem coword_mul_unit (b γ δ : List (Fin 2)) :
    C.coword b * C.unit γ δ = 0 ∨ ∃ γ', C.coword b * C.unit γ δ = C.unit γ' δ := by
  induction b generalizing γ with
  | nil => exact Or.inr ⟨γ, by rw [coword_nil, one_mul]⟩
  | cons a b ih =>
    cases γ with
    | nil =>
      left
      rw [coword_cons, unit, word_nil, one_mul, mul_assoc, ← mul_assoc (C.gs a), gs_mul_p,
        zero_mul, mul_zero]
    | cons d γ =>
      have h : C.coword (a :: b) * C.unit (d :: γ) δ =
          C.coword b * (C.gs a * C.gen d) * C.unit γ δ := by
        simp only [coword_cons, unit, word_cons, mul_assoc]
      rw [h, gs_mul_gen]
      by_cases had : a = d
      · rw [if_pos had, mul_one]
        exact ih γ
      · left
        rw [if_neg had, mul_zero, zero_mul]

theorem unit_mul_word (γ δ a : List (Fin 2)) :
    C.unit γ δ * C.word a = 0 ∨ ∃ δ', C.unit γ δ * C.word a = C.unit γ δ' := by
  induction a generalizing δ with
  | nil => exact Or.inr ⟨δ, by rw [word_nil, mul_one]⟩
  | cons d a ih =>
    cases δ with
    | nil =>
      left
      rw [unit, coword_nil, mul_one, word_cons, mul_assoc, ← mul_assoc C.p, p_mul_gen,
        zero_mul, mul_zero]
    | cons b δ =>
      have h : C.unit γ (b :: δ) * C.word (d :: a) =
          C.unit γ δ * (C.gs b * C.gen d) * C.word a := by
        simp only [unit, coword_cons, word_cons, mul_assoc]
      rw [h, gs_mul_gen]
      by_cases hbd : b = d
      · rw [if_pos hbd, mul_one]
        exact ih δ
      · left
        rw [if_neg hbd, mul_zero, zero_mul]

theorem word_mul_unit (a γ δ : List (Fin 2)) : C.word a * C.unit γ δ = C.unit (a ++ γ) δ := by
  simp only [unit, word_append, mul_assoc]

theorem unit_mul_coword (γ δ b : List (Fin 2)) :
    C.unit γ δ * C.coword b = C.unit γ (b ++ δ) := by
  simp only [unit, coword_append, mul_assoc]

/-- The `F_2`-span of the monomials `α β*`. -/
def monomialSpan : Submodule (ZMod 2) R :=
  Submodule.span (ZMod 2)
    (Set.range fun ab : List (Fin 2) × List (Fin 2) ↦ C.word ab.1 * C.coword ab.2)

theorem mul_unit_mem (hspan : ∀ r : R, r ∈ C.monomialSpan) (r : R) (γ δ : List (Fin 2)) :
    r * C.unit γ δ ∈ C.unitSpan := by
  have hr := hspan r
  rw [monomialSpan] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    show C.word a * C.coword b * C.unit γ δ ∈ C.unitSpan
    rw [mul_assoc]
    rcases C.coword_mul_unit b γ δ with h | ⟨γ', h⟩
    · rw [h, mul_zero]
      exact C.unitSpan.zero_mem
    · rw [h, word_mul_unit]
      exact C.unit_mem_unitSpan _ _
  | zero =>
    rw [zero_mul]
    exact C.unitSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.unitSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact C.unitSpan.smul_mem c hx

theorem unit_mul_mem (hspan : ∀ r : R, r ∈ C.monomialSpan) (r : R) (γ δ : List (Fin 2)) :
    C.unit γ δ * r ∈ C.unitSpan := by
  have hr := hspan r
  rw [monomialSpan] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    show C.unit γ δ * (C.word a * C.coword b) ∈ C.unitSpan
    rw [← mul_assoc]
    rcases C.unit_mul_word γ δ a with h | ⟨δ', h⟩
    · rw [h, zero_mul]
      exact C.unitSpan.zero_mem
    · rw [h, unit_mul_coword]
      exact C.unit_mem_unitSpan _ _
  | zero =>
    rw [mul_zero]
    exact C.unitSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact C.unitSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact C.unitSpan.smul_mem c hx

theorem mul_mem_unitSpan (hspan : ∀ r : R, r ∈ C.monomialSpan) (r : R) {x : R}
    (hx : x ∈ C.unitSpan) : r * x ∈ C.unitSpan := by
  rw [unitSpan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨γ, δ⟩, rfl⟩ := hx
    exact C.mul_unit_mem hspan r γ δ
  | zero =>
    rw [mul_zero]
    exact C.unitSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact C.unitSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact C.unitSpan.smul_mem c hx

theorem mul_mem_unitSpan' (hspan : ∀ r : R, r ∈ C.monomialSpan) (r : R) {x : R}
    (hx : x ∈ C.unitSpan) : x * r ∈ C.unitSpan := by
  rw [unitSpan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨γ, δ⟩, rfl⟩ := hx
    exact C.unit_mul_mem hspan r γ δ
  | zero =>
    rw [zero_mul]
    exact C.unitSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.unitSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact C.unitSpan.smul_mem c hx

theorem mem_unitSpan_of_mem_span_p (hspan : ∀ r : R, r ∈ C.monomialSpan) {x : R}
    (hx : x ∈ TwoSidedIdeal.span {C.p}) : x ∈ C.unitSpan := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    have hp := C.unit_mem_unitSpan [] []
    rw [unit_nil_nil] at hp
    rw [hx]
    exact hp
  | zero => exact C.unitSpan.zero_mem
  | add x y _ _ hx hy => exact C.unitSpan.add_mem hx hy
  | neg x _ hx => exact C.unitSpan.neg_mem hx
  | left_absorb a x _ hx => exact C.mul_mem_unitSpan hspan a hx
  | right_absorb b x _ hx => exact C.mul_mem_unitSpan' hspan b hx

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.coword_mul_unit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mul_word
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.word_mul_unit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mul_coword
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.mul_unit_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mul_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.mul_mem_unitSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.mul_mem_unitSpan'
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.mem_unitSpan_of_mem_span_p
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.monomialSpan
