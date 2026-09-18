import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoBruhatSteps
import GroupApproximation.Meta.AxiomGuard

/-!
# Bruhat decomposition of `St_I(𝔽₂)` (lane sk-leavitt-23)

Assume a third index exists.  `Bru L` is stable under left multiplication by the row roots
`x_Lb(1)` (`bru_row_mul`), hence by every root (`bru_gen_mul`).  Since `Bru L 1` holds, every
element of `St_I(𝔽₂)` lies in `U P ∪ ⋃_j S w_j P` (`bru_all`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `x_Lb(1) · A_b = A_b · w_b`, with `A_b = x_bL(1)`. -/
theorem row_mul_col_eq {L b : I} (hLb : L ≠ b) :
    x L b hLb (1 : ZMod 2) * x b L hLb.symm 1 = x b L hLb.symm 1 * weyl b L hLb.symm := by
  unfold weyl
  rw [← mul_assoc, ← mul_assoc, WeylCalc.x_mul_self two_eq_zero b L hLb.symm 1, one_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.row_mul_col_eq

theorem bru_row_mul_swp (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {L b j : I}
    (hLb : L ≠ b) (hj : j ≠ L) {s p : SteinbergGroup I (ZMod 2)} (hs : s ∈ levSpan L)
    (hp : p ∈ parSpan L) : Bru L (x L b hLb (1 : ZMod 2) * (s * weyl j L hj * p)) := by
  have ht : s⁻¹ * x L b hLb (1 : ZMod 2) * s ∈ rowSpan L := by
    have h := lev_conj_row (Subgroup.inv_mem _ hs)
      (x_mem_rootSpan (p := fun i _ => i = L) hLb (1 : ZMod 2) rfl)
    rwa [inv_inv] at h
  obtain ⟨d, v', hv', e⟩ := row_split hj ht
  have hC := weyl_conj_rowExcept hthird hj hv'
  have key : x L b hLb (1 : ZMod 2) * (s * weyl j L hj * p) =
      s * (x L j hj.symm d * weyl j L hj) * (weyl j L hj * v' * (weyl j L hj)⁻¹ * p) := by
    calc x L b hLb (1 : ZMod 2) * (s * weyl j L hj * p)
        = s * (s⁻¹ * x L b hLb (1 : ZMod 2) * s) * weyl j L hj * p := by group
      _ = s * x L j hj.symm d * (v' * weyl j L hj) * p := by rw [e]; simp only [mul_assoc]
      _ = s * (x L j hj.symm d * weyl j L hj) *
          (weyl j L hj * v' * (weyl j L hj)⁻¹ * p) := by
          rw [weyl_mul_conj hj v']; simp only [mul_assoc]
  rw [key]
  rcases zmod_two_cases d with rfl | rfl
  · rw [x_zero, one_mul]
    exact Or.inr ⟨j, hj, s, hs, weyl j L hj * v' * (weyl j L hj)⁻¹ * p,
      Subgroup.mul_mem _ hC hp, rfl⟩
  · rw [row_mul_weyl hthird hj]
    refine Or.inl ⟨s * x j L hj 1 * s⁻¹,
      lev_conj_col hs (x_mem_rootSpan (p := fun _ k => k = L) hj (1 : ZMod 2) rfl),
      s * x L j hj.symm 1 * (weyl j L hj * v' * (weyl j L hj)⁻¹ * p), ?_, by group⟩
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (lev_le_par hs)
        (x_mem_rootSpan (p := fun _ k => k ≠ L) hj.symm (1 : ZMod 2) hj))
      (Subgroup.mul_mem _ hC hp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_row_mul_swp

theorem bru_row_mul_up (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {L b : I}
    (hLb : L ≠ b) {u p : SteinbergGroup I (ZMod 2)} (hu : u ∈ colSpan L)
    (hp : p ∈ parSpan L) : Bru L (x L b hLb (1 : ZMod 2) * (u * p)) := by
  obtain ⟨d, u', hu', rfl⟩ := col_split hLb.symm hu
  have hN : u'⁻¹ * x L b hLb (1 : ZMod 2) * u' ∈ parSpan L := by
    have h := colExcept_conj_colAt hLb.symm (Subgroup.inv_mem _ hu')
      (x_mem_rootSpan (p := fun _ l => l = b) hLb (1 : ZMod 2) rfl)
    rw [inv_inv] at h
    exact rootSpan_mono (p := fun _ l => l = b)
      (fun _ l _ (hl : l = b) => by rw [hl]; exact hLb.symm) h
  have hU : u' ∈ colSpan L :=
    rootSpan_mono (p := fun i k => k = L ∧ i ≠ b) (fun _ _ _ hq => hq.1) hu'
  rcases zmod_two_cases d with rfl | rfl
  · refine Or.inl ⟨u', hU, u'⁻¹ * x L b hLb (1 : ZMod 2) * u' * p,
      Subgroup.mul_mem _ hN hp, ?_⟩
    rw [x_zero, one_mul]
    group
  · obtain ⟨s₁, hs₁, hs₁e⟩ : ∃ s₁ : SteinbergGroup I (ZMod 2), s₁ ∈ levSpan L ∧
        s₁ = weyl b L hLb.symm * u' * (weyl b L hLb.symm)⁻¹ :=
      ⟨_, weyl_conj_colExcept hthird hLb.symm hu', rfl⟩
    have hu₁ : s₁⁻¹ * x b L hLb.symm (1 : ZMod 2) * s₁ ∈ colSpan L := by
      have h := lev_conj_col (Subgroup.inv_mem _ hs₁)
        (x_mem_rootSpan (p := fun _ k => k = L) hLb.symm (1 : ZMod 2) rfl)
      rwa [inv_inv] at h
    obtain ⟨p', hp', e⟩ := col_mul_weyl_mem hthird hLb.symm hu₁
    refine Or.inr ⟨b, hLb.symm, s₁, hs₁, p' * p, Subgroup.mul_mem _ hp' hp, ?_⟩
    calc x L b hLb (1 : ZMod 2) * (x b L hLb.symm 1 * u' * p)
        = x L b hLb (1 : ZMod 2) * x b L hLb.symm 1 * u' * p := by simp only [mul_assoc]
      _ = x b L hLb.symm 1 * weyl b L hLb.symm * u' * p := by rw [row_mul_col_eq hLb]
      _ = s₁ * (s₁⁻¹ * x b L hLb.symm (1 : ZMod 2) * s₁ * weyl b L hLb.symm) * p := by
          rw [hs₁e]; group
      _ = s₁ * (weyl b L hLb.symm * p') * p := by rw [e]
      _ = s₁ * weyl b L hLb.symm * (p' * p) := by simp only [mul_assoc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_row_mul_up

theorem bru_gen_mul (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {L : I} (i j : I) (h : i ≠ j)
    (c : ZMod 2) {g : SteinbergGroup I (ZMod 2)} (hg : Bru L g) : Bru L (x i j h c * g) := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [x_zero, one_mul]
    exact hg
  · by_cases hiL : i = L
    · have hLj : L ≠ j := by rw [← hiL]; exact h
      rw [WeylCalc.x_congr hiL rfl h hLj (1 : ZMod 2)]
      rcases hg with ⟨u, hu, p, hp, rfl⟩ | ⟨k, hk, s, hs, p, hp, rfl⟩
      · exact bru_row_mul_up hthird hLj hu hp
      · exact bru_row_mul_swp hthird hLj hk hs hp
    · by_cases hjL : j = L
      · exact bru_col_mul hthird (x_mem_rootSpan h (1 : ZMod 2) hjL) hg
      · exact bru_lev_mul (x_mem_rootSpan h (1 : ZMod 2) ⟨hiL, hjL⟩) hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_gen_mul

/-- **Bruhat decomposition.**  Every element of `St_I(𝔽₂)` lies in `U P` or in some
`S w_j P`. -/
theorem bru_all (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) (L : I)
    (g : SteinbergGroup I (ZMod 2)) : Bru L g := by
  have key := rootSpan_induction (p := fun _ _ : I => True)
    (Q := fun g => ∀ y : SteinbergGroup I (ZMod 2), Bru L y → Bru L (g * y))
    (fun i j h a _ y hy => bru_gen_mul hthird i j h a hy)
    (fun y hy => by rw [one_mul]; exact hy)
    (fun g k _ _ hg hk y hy => by rw [mul_assoc]; exact hg _ (hk y hy))
    (mem_rootSpan_true g)
  simpa only [mul_one] using key 1 (bru_one L)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_all

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
