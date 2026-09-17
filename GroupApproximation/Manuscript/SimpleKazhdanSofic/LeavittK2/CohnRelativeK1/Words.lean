import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Cohn words and the matrix units `α p β*`

Lane `sk-leavitt-19` (relative `K_1(C_2, I) = 0`), first module.

In a ring `R` with elements `e, f, e*, f*` satisfying the Cohn relations
`e*e = f*f = 1`, `e*f = f*e = 0`, put `p = 1 - ee* - ff*`.  For a word
`α = a_1 ⋯ a_n` in `{0, 1}` write `α = g_{a_1} ⋯ g_{a_n}` (`word`) and
`α* = g*_{a_n} ⋯ g*_{a_1}` (`coword`).  The basic identity is the sandwich

  `p β* γ p = δ_{β γ} p`,

which makes `u(α, β) = α p β*` a system of matrix units:
`u(α, β) u(γ, δ) = δ_{β γ} u(α, δ)`.  This is the local-unit structure of the
ideal `I = (p)` of the Cohn path algebra used by the excision argument.

The structure `CohnTwoData` only records the four defining relations of the
Cohn algebra (no part of the claim is bundled).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

/-- Four elements of a ring satisfying the defining relations of the Cohn path
algebra `C_2`: `e*e = f*f = 1` and `e*f = f*e = 0`. -/
structure CohnTwoData (R : Type*) [Ring R] where
  e : R
  f : R
  es : R
  fs : R
  es_e : es * e = 1
  fs_f : fs * f = 1
  es_f : es * f = 0
  fs_e : fs * e = 0

namespace CohnTwoData

variable {R : Type*} [Ring R]

theorem fin_two_cases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide

/-- The generator `g_a` (`g_0 = e`, `g_1 = f`). -/
def gen (C : CohnTwoData R) (a : Fin 2) : R := if a = 0 then C.e else C.f

/-- The adjoint generator `g*_a`. -/
def gs (C : CohnTwoData R) (a : Fin 2) : R := if a = 0 then C.es else C.fs

/-- The projection `p = 1 - ee* - ff*`. -/
def p (C : CohnTwoData R) : R := 1 - C.e * C.es - C.f * C.fs

/-- The word `α = g_{a_1} ⋯ g_{a_n}`. -/
def word (C : CohnTwoData R) : List (Fin 2) → R
  | [] => 1
  | a :: α => C.gen a * word C α

/-- The coword `α* = g*_{a_n} ⋯ g*_{a_1}`. -/
def coword (C : CohnTwoData R) : List (Fin 2) → R
  | [] => 1
  | a :: α => coword C α * C.gs a

/-- The matrix unit `u(α, β) = α p β*`. -/
def unit (C : CohnTwoData R) (α β : List (Fin 2)) : R :=
  C.word α * C.p * C.coword β

variable (C : CohnTwoData R)

theorem gen_zero : C.gen 0 = C.e := if_pos rfl
theorem gen_one : C.gen 1 = C.f := if_neg (by decide)
theorem gs_zero : C.gs 0 = C.es := if_pos rfl
theorem gs_one : C.gs 1 = C.fs := if_neg (by decide)

theorem word_nil : C.word [] = 1 := rfl
theorem word_cons (a : Fin 2) (α : List (Fin 2)) :
    C.word (a :: α) = C.gen a * C.word α := rfl
theorem coword_nil : C.coword [] = 1 := rfl
theorem coword_cons (a : Fin 2) (α : List (Fin 2)) :
    C.coword (a :: α) = C.coword α * C.gs a := rfl

theorem gs_mul_gen (a b : Fin 2) : C.gs a * C.gen b = if a = b then 1 else 0 := by
  rcases fin_two_cases a with rfl | rfl <;> rcases fin_two_cases b with rfl | rfl
  · rw [gs_zero, gen_zero, C.es_e, if_pos rfl]
  · rw [gs_zero, gen_one, C.es_f, if_neg (by decide)]
  · rw [gs_one, gen_zero, C.fs_e, if_neg (by decide)]
  · rw [gs_one, gen_one, C.fs_f, if_pos rfl]

theorem p_mul_e : C.p * C.e = 0 := by
  simp only [p, sub_mul, one_mul, mul_assoc, C.es_e, C.fs_e, mul_one, mul_zero, sub_self,
    sub_zero]

theorem p_mul_f : C.p * C.f = 0 := by
  simp only [p, sub_mul, one_mul, mul_assoc, C.es_f, C.fs_f, mul_one, mul_zero, sub_self,
    sub_zero]

theorem es_mul_p : C.es * C.p = 0 := by
  simp only [p, mul_sub, mul_one, ← mul_assoc, C.es_e, C.es_f, one_mul, zero_mul, sub_self,
    sub_zero]

theorem fs_mul_p : C.fs * C.p = 0 := by
  simp only [p, mul_sub, mul_one, ← mul_assoc, C.fs_e, C.fs_f, one_mul, zero_mul, sub_self,
    sub_zero]

theorem p_mul_gen (a : Fin 2) : C.p * C.gen a = 0 := by
  rcases fin_two_cases a with rfl | rfl
  · rw [gen_zero]; exact C.p_mul_e
  · rw [gen_one]; exact C.p_mul_f

theorem gs_mul_p (a : Fin 2) : C.gs a * C.p = 0 := by
  rcases fin_two_cases a with rfl | rfl
  · rw [gs_zero]; exact C.es_mul_p
  · rw [gs_one]; exact C.fs_mul_p

theorem p_mul_p : C.p * C.p = C.p := by
  calc C.p * C.p = C.p * (1 - C.e * C.es - C.f * C.fs) := rfl
    _ = C.p - C.p * C.e * C.es - C.p * C.f * C.fs := by simp only [mul_sub, mul_one, ← mul_assoc]
    _ = C.p := by rw [C.p_mul_e, C.p_mul_f, zero_mul, zero_mul, sub_zero, sub_zero]

theorem word_append (α β : List (Fin 2)) : C.word (α ++ β) = C.word α * C.word β := by
  induction α with
  | nil => rw [List.nil_append, word_nil, one_mul]
  | cons a α ih => rw [List.cons_append, word_cons, word_cons, ih, mul_assoc]

theorem coword_append (α β : List (Fin 2)) :
    C.coword (α ++ β) = C.coword β * C.coword α := by
  induction α with
  | nil => rw [List.nil_append, coword_nil, mul_one]
  | cons a α ih => rw [List.cons_append, coword_cons, coword_cons, ih, mul_assoc]

theorem coword_cons_mul_word_cons (a b : Fin 2) (β γ : List (Fin 2)) :
    C.coword (a :: β) * C.word (b :: γ) = if a = b then C.coword β * C.word γ else 0 := by
  have h : C.coword (a :: β) * C.word (b :: γ) = C.coword β * (C.gs a * C.gen b) * C.word γ := by
    simp only [coword_cons, word_cons, mul_assoc]
  rw [h, gs_mul_gen]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, mul_one]
  · rw [if_neg hab, if_neg hab, mul_zero, zero_mul]

/-- **Sandwich identity** `p β* γ p = δ_{βγ} p`. -/
theorem sandwich (β γ : List (Fin 2)) :
    C.p * (C.coword β * (C.word γ * C.p)) = if β = γ then C.p else 0 := by
  induction β generalizing γ with
  | nil =>
    cases γ with
    | nil => rw [coword_nil, word_nil, one_mul, one_mul, p_mul_p, if_pos rfl]
    | cons b γ =>
      rw [coword_nil, one_mul, word_cons, mul_assoc, ← mul_assoc C.p, p_mul_gen, zero_mul,
        if_neg (List.cons_ne_nil b γ).symm]
  | cons a β ih =>
    cases γ with
    | nil =>
      rw [word_nil, one_mul, coword_cons, mul_assoc, C.gs_mul_p, mul_zero, mul_zero,
        if_neg (List.cons_ne_nil a β)]
    | cons b γ =>
      rw [← mul_assoc (C.coword (a :: β)), coword_cons_mul_word_cons]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, mul_assoc, ih γ]
        simp only [List.cons.injEq, eq_self_iff_true, true_and]
      · have hne : ¬ (a :: β = b :: γ) := fun hc ↦ hab (List.cons.inj hc).1
        rw [if_neg hab, zero_mul, mul_zero, if_neg hne]

theorem unit_nil_nil : C.unit [] [] = C.p := by
  rw [unit, word_nil, coword_nil, one_mul, mul_one]

/-- **Matrix units**: `u(α, β) u(γ, δ) = δ_{βγ} u(α, δ)`. -/
theorem unit_mul_unit (α β γ δ : List (Fin 2)) :
    C.unit α β * C.unit γ δ = if β = γ then C.unit α δ else 0 := by
  have h : C.unit α β * C.unit γ δ =
      C.word α * (C.p * (C.coword β * (C.word γ * C.p))) * C.coword δ := by
    simp only [unit, mul_assoc]
  rw [h, sandwich]
  by_cases hβγ : β = γ
  · rw [if_pos hβγ, if_pos hβγ, unit]
  · rw [if_neg hβγ, if_neg hβγ, mul_zero, zero_mul]

/-- **Coefficient extraction** `p α* u(α', β') β p = δ_{αα'} δ_{β'β} p`. -/
theorem extract (α α' β' β : List (Fin 2)) :
    C.p * (C.coword α * (C.unit α' β' * (C.word β * C.p))) =
      if α = α' ∧ β' = β then C.p else 0 := by
  have h : C.p * (C.coword α * (C.unit α' β' * (C.word β * C.p))) =
      (C.p * (C.coword α * (C.word α' * C.p))) * (C.p * (C.coword β' * (C.word β * C.p))) := by
    calc C.p * (C.coword α * (C.unit α' β' * (C.word β * C.p)))
        = C.p * (C.coword α * (C.word α' * ((C.p * C.p) * (C.coword β' * (C.word β * C.p))))) := by
          rw [C.p_mul_p]; simp only [unit, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  rw [h, sandwich, sandwich]
  by_cases h1 : α = α'
  · by_cases h2 : β' = β
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, C.p_mul_p]
    · rw [if_pos h1, if_neg h2, if_neg (fun h ↦ h2 h.2), mul_zero]
  · rw [if_neg h1, if_neg (fun h ↦ h1 h.1), zero_mul]

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.sandwich
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mul_unit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.extract
