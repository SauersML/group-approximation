import GroupApproximation.Leavitt.AryWindowReduction

/-!
# Degree windows are multiplicative, at arbitrary arity

`KOne/WindowProductClosure.lean` over a complete matrix family `F` on any index type:
the span of a degree window is closed under products with the windows adding.
Monomials multiply by the prefix trichotomy --- a collapse to a longer `s`-word, a
collapse to a longer `t`-word, or zero --- and in each case the degree of the product
is the sum of the degrees.  Nothing in the argument sees the size of the alphabet.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

/-- Monomial times window span. -/
theorem monomial_mul_mem_span {lo' hi' : ℤ} (a b : List ι)
    {y : A} (hy : y ∈ Submodule.span k (F.degreeMonomials lo' hi')) :
    F.wordS a * F.wordT b * y ∈ Submodule.span k
      (F.degreeMonomials
        ((a.length : ℤ) - b.length + lo')
        ((a.length : ℤ) - b.length + hi')) := by
  induction hy using Submodule.span_induction with
  | mem y hymem =>
      obtain ⟨c, d, hl, hh, rfl⟩ := hymem
      by_cases h1 : b <+: c
      · obtain ⟨e, rfl⟩ := h1
        have hcollapse : F.wordS a * F.wordT b *
            (F.wordS (b ++ e) * F.wordT d) =
            F.wordS (a ++ e) * F.wordT d := by
          rw [show F.wordS a * F.wordT b *
            (F.wordS (b ++ e) * F.wordT d) =
            F.wordS a * (F.wordT b * F.wordS (b ++ e)) * F.wordT d
            from by noncomm_ring, F.wordT_mul_wordS_append_left,
            ← F.wordS_append]
        rw [hcollapse]
        refine Submodule.subset_span ⟨a ++ e, d, ?_, ?_, rfl⟩
        · simp only [List.length_append] at hl hh ⊢
          push_cast at hl hh ⊢
          omega
        · simp only [List.length_append] at hl hh ⊢
          push_cast at hl hh ⊢
          omega
      · by_cases h2 : c <+: b
        · obtain ⟨f, rfl⟩ := h2
          have hcollapse : F.wordS a * F.wordT (c ++ f) *
              (F.wordS c * F.wordT d) =
              F.wordS a * F.wordT (d ++ f) := by
            rw [show F.wordS a * F.wordT (c ++ f) *
              (F.wordS c * F.wordT d) =
              F.wordS a * (F.wordT (c ++ f) * F.wordS c) * F.wordT d
              from by noncomm_ring, F.wordT_append_mul_wordS,
              show F.wordS a * F.wordT f * F.wordT d =
                F.wordS a * (F.wordT f * F.wordT d) from by
                  noncomm_ring, ← F.wordT_append]
          rw [hcollapse]
          refine Submodule.subset_span ⟨a, d ++ f, ?_, ?_, rfl⟩
          · simp only [List.length_append] at hl hh ⊢
            push_cast at hl hh ⊢
            omega
          · simp only [List.length_append] at hl hh ⊢
            push_cast at hl hh ⊢
            omega
        · have hzero : F.wordT b * F.wordS c = 0 :=
            F.wordT_mul_wordS_of_incomparable b c h1 h2
          rw [show F.wordS a * F.wordT b * (F.wordS c * F.wordT d) =
            F.wordS a * (F.wordT b * F.wordS c) * F.wordT d from by
              noncomm_ring, hzero]
          rw [show F.wordS a * (0 : A) * F.wordT d = 0 from by
            noncomm_ring]
          exact Submodule.zero_mem _
  | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
  | add y₁ y₂ _ _ hy₁ hy₂ =>
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
  | smul r y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy

/-- **Windows multiply**: the product of window spans lands in the sum window. -/
theorem window_mul_mem_span {lo hi lo' hi' : ℤ} {x y : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials lo hi))
    (hy : y ∈ Submodule.span k (F.degreeMonomials lo' hi')) :
    x * y ∈ Submodule.span k
      (F.degreeMonomials (lo + lo') (hi + hi')) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      have := F.monomial_mul_mem_span (k := k) a b hy
      refine F.span_degreeMonomials_mono ?_ ?_ this
      · omega
      · omega
  | zero =>
      rw [zero_mul]
      exact Submodule.zero_mem _
  | add x₁ x₂ _ _ hx₁ hx₂ =>
      rw [add_mul]
      exact Submodule.add_mem _ hx₁ hx₂
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_mul_mem_span
#audit_axioms GroupApproximation.CompleteMatrixFamily.window_mul_mem_span
