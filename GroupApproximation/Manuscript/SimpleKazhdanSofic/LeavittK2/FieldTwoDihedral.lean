import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoStab
import GroupApproximation.Meta.AxiomGuard

/-!
# `St_3(𝔽₂)` acts faithfully on `𝔽₂³` (lane sk-leavitt-23)

`Inj N` says that an element of `St_N(𝔽₂)` acting trivially on `𝔽₂^N` is trivial.

In `St_3(𝔽₂)` put `A = x_01(1)` and `B = x_10(1)`.  Then `A² = B² = 1` and `ABABA = B`
(`weyl_braid_two`), so the six words `1, A, B, AB, BA, ABA` are closed under right
multiplication by `A` and `B` (`dih_mul`).  Hence `levSpan 2 = ⟨A, B⟩` consists of these six
words (`dih_of_lev`).  An element acting trivially lies in `levSpan 2` (`mem_levSpan_of_act`).
Each nontrivial word moves a basis vector, which gives `inj_three`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

/-- Faithfulness of the vector action of `St_N(𝔽₂)`. -/
def Inj (N : ℕ) : Prop :=
  ∀ g : SteinbergGroup (Fin N) (ZMod 2), (∀ v : Fin N → ZMod 2, act g v = v) → g = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.Inj

/-- The six words `1, a, b, ab, ba, aba`. -/
def Dih {G : Type*} [Group G] (a b g : G) : Prop :=
  g = 1 ∨ g = a ∨ g = b ∨ g = a * b ∨ g = b * a ∨ g = a * b * a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.Dih

theorem dih_mul {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a * b * a = b) {g : G} (hg : Dih a b g) :
    Dih a b (g * a) ∧ Dih a b (g * b) := by
  have h1 : a * b * a * b = b * a := by
    calc a * b * a * b = a * b * a * b * a * a := by
          rw [mul_assoc (a * b * a * b) a a, ha, mul_one]
      _ = b * a := by rw [hab]
  have h2 : b * a * b = a * b * a := by
    calc b * a * b = a * a * (b * a * b) := by rw [ha, one_mul]
      _ = a * (a * b * a * b) := by simp only [mul_assoc]
      _ = a * b * a := by rw [h1]; simp only [mul_assoc]
  unfold Dih at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Or.inr (Or.inl (one_mul _)), Or.inr (Or.inr (Or.inl (one_mul _)))⟩
  · exact ⟨Or.inl ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), Or.inl hb⟩
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), Or.inr (Or.inl ?_)⟩
    rw [mul_assoc, hb, mul_one]
  · refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))⟩
    rw [mul_assoc, ha, mul_one]
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ?_))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))⟩
    rw [mul_assoc, ha, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.dih_mul

theorem zero_ne_one_fin_three : (0 : Fin 3) ≠ 1 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.zero_ne_one_fin_three

/-- `A = x_01(1)` in `St_3(𝔽₂)`. -/
abbrev dA : SteinbergGroup (Fin 3) (ZMod 2) := x 0 1 zero_ne_one_fin_three 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.dA

/-- `B = x_10(1)` in `St_3(𝔽₂)`. -/
abbrev dB : SteinbergGroup (Fin 3) (ZMod 2) := x 1 0 zero_ne_one_fin_three.symm 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.dB

theorem third_fin_three : ∀ a b : Fin 3, ∃ m : Fin 3, m ≠ a ∧ m ≠ b := fun a b =>
  WeylCalc.exists_third (le_refl 3) a b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.third_fin_three

/-- `levSpan 2 ⊆ {1, A, B, AB, BA, ABA}`. -/
theorem dih_of_lev {g : SteinbergGroup (Fin 3) (ZMod 2)} (hg : g ∈ levSpan (2 : Fin 3)) :
    Dih dA dB g := by
  have hA : dA * dA = 1 := WeylCalc.x_mul_self two_eq_zero 0 1 zero_ne_one_fin_three 1
  have hB : dB * dB = 1 := WeylCalc.x_mul_self two_eq_zero 1 0 zero_ne_one_fin_three.symm 1
  have hAB : dA * dB * dA * dB * dA = dB := weyl_braid_two third_fin_three zero_ne_one_fin_three
  have key : ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    decide
  have hQ := rootSpan_induction (p := fun i j : Fin 3 => i ≠ 2 ∧ j ≠ 2)
    (Q := fun t => ∀ d, Dih dA dB d → Dih dA dB (d * t))
    (fun i j h c (hp : i ≠ 2 ∧ j ≠ 2) d hd => by
      rcases key i j hp.1 hp.2 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases zmod_two_cases c with rfl | rfl
        · rw [x_zero, mul_one]
          exact hd
        · exact (dih_mul hA hB hAB hd).1
      · rcases zmod_two_cases c with rfl | rfl
        · rw [x_zero, mul_one]
          exact hd
        · exact (dih_mul hA hB hAB hd).2)
    (fun d hd => by rw [mul_one]; exact hd)
    (fun g k _ _ hg hk d hd => by rw [← mul_assoc]; exact hk _ (hg d hd)) hg
  have h := hQ 1 (by unfold Dih; exact Or.inl rfl)
  rwa [one_mul] at h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.dih_of_lev

/-- `St_3(𝔽₂)` acts faithfully on `𝔽₂³`. -/
theorem inj_three : Inj 3 := by
  intro g hg
  have hD := dih_of_lev (mem_levSpan_of_act third_fin_three 2 hg)
  unfold Dih at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · have e := congrFun (hg (unitVec 1)) 0
    simp only [dA, act_x_apply] at e <;>
      exact absurd e (by decide)
  · have e := congrFun (hg (unitVec 0)) 1
    simp only [dB, act_x_apply] at e <;>
      exact absurd e (by decide)
  · have e := congrFun (hg (unitVec 0)) 1
    simp only [dA, dB, act_mul, act_x_apply] at e <;>
      exact absurd e (by decide)
  · have e := congrFun (hg (unitVec 1)) 0
    simp only [dA, dB, act_mul, act_x_apply] at e <;>
      exact absurd e (by decide)
  · have e := congrFun (hg (unitVec 1)) 0
    simp only [dA, dB, act_mul, act_x_apply] at e <;>
      exact absurd e (by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.inj_three

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
