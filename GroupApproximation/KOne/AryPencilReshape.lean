import GroupApproximation.KOne.AryCodeChangeUnits
import GroupApproximation.KOne.AryWindowProductClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Reshaping a code pencil, at arbitrary arity

`KOne/PencilReshape.lean` over a complete matrix family on an alphabet `ι`: the entries of a
code pencil can be carried from a pair of complete codes `(R, C)` to any other pair `(P, Q)`
of the same sizes, at the cost of multiplying by the two code-change units
`∑ᵢ s_{Pᵢ} t_{Rᵢ}` and `∑ⱼ s_{Cⱼ} t_{Qⱼ}`.  Both lie in `centralClassGroup` by
`codeChange_mem_centralClassGroup`, so membership in the class group does not see the
reshaping.  The value window of the reshaped pencil is read off from word lengths
(`pencilVal_window_mem`).
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

section CodeChange

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

theorem codeChange_mul_eq_one (P R : AryPrefixCode ρ ι) (hP : F.IsComplete P) :
    (∑ i, F.wordS (P.word i) * F.wordT (R.word i)) *
      (∑ i, F.wordS (R.word i) * F.wordT (P.word i)) = 1 := by
  rw [Finset.sum_mul]
  calc ∑ i, F.wordS (P.word i) * F.wordT (R.word i) *
        ∑ i', F.wordS (R.word i') * F.wordT (P.word i')
      = ∑ i, F.wordS (P.word i) * F.wordT (P.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_eq_single i]
        · rw [show F.wordS (P.word i) * F.wordT (R.word i) *
              (F.wordS (R.word i) * F.wordT (P.word i)) =
            F.wordS (P.word i) * (F.wordT (R.word i) * F.wordS (R.word i)) *
              F.wordT (P.word i) by simp only [mul_assoc], F.wordT_mul_wordS_self, mul_one]
        · intro i' _ hi'
          rw [show F.wordS (P.word i) * F.wordT (R.word i) *
              (F.wordS (R.word i') * F.wordT (P.word i')) =
            F.wordS (P.word i) * (F.wordT (R.word i) * F.wordS (R.word i')) *
              F.wordT (P.word i') by simp only [mul_assoc], F.prefixCode_orthogonal R i i',
            if_neg (Ne.symm hi'), mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i) h
    _ = 1 := hP

/-- The code-change unit `∑ᵢ s_{Pᵢ} t_{Rᵢ}` between two complete codes of the same index
type. -/
noncomputable def codeChangeUnit (P R : AryPrefixCode ρ ι) (hP : F.IsComplete P)
    (hR : F.IsComplete R) : Aˣ where
  val := ∑ i, F.wordS (P.word i) * F.wordT (R.word i)
  inv := ∑ i, F.wordS (R.word i) * F.wordT (P.word i)
  val_inv := F.codeChange_mul_eq_one P R hP
  inv_val := F.codeChange_mul_eq_one R P hR

/-- A code change on the left carries the row code of a code pencil. -/
theorem codeChange_mul_codePencil {κ : Type*} [Fintype κ] (P R : AryPrefixCode ρ ι)
    (W : κ → List ι) (E : ρ → κ → A) :
    (∑ i, F.wordS (P.word i) * F.wordT (R.word i)) *
      (∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (W j)) =
    ∑ i, ∑ j, F.wordS (P.word i) * E i j * F.wordT (W j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show F.wordS (P.word i) * F.wordT (R.word i) *
        (F.wordS (R.word i) * E i j * F.wordT (W j)) =
      F.wordS (P.word i) * (F.wordT (R.word i) * F.wordS (R.word i)) * E i j *
        F.wordT (W j) by simp only [mul_assoc], F.wordT_mul_wordS_self, mul_one]
  · intro i' _ hi'
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [show F.wordS (P.word i) * F.wordT (R.word i) *
        (F.wordS (R.word i') * E i' j * F.wordT (W j)) =
      F.wordS (P.word i) * (F.wordT (R.word i) * F.wordS (R.word i')) * E i' j *
        F.wordT (W j) by simp only [mul_assoc], F.prefixCode_orthogonal R i i',
      if_neg (Ne.symm hi'), mul_zero, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CodeChange

/-- A code change on the right carries the column code of a code pencil. -/
theorem codePencil_mul_codeChange {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (V : ρ → List ι) (C Q : AryPrefixCode κ ι) (E : ρ → κ → A) :
    (∑ i, ∑ j, F.wordS (V i) * E i j * F.wordT (C.word j)) *
      (∑ j, F.wordS (C.word j) * F.wordT (Q.word j)) =
    ∑ i, ∑ j, F.wordS (V i) * E i j * F.wordT (Q.word j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [show F.wordS (V i) * E i j * F.wordT (C.word j) *
        (F.wordS (C.word j) * F.wordT (Q.word j)) =
      F.wordS (V i) * E i j * (F.wordT (C.word j) * F.wordS (C.word j)) *
        F.wordT (Q.word j) by simp only [mul_assoc], F.wordT_mul_wordS_self, mul_one]
  · intro j' _ hj'
    rw [show F.wordS (V i) * E i j * F.wordT (C.word j) *
        (F.wordS (C.word j') * F.wordT (Q.word j')) =
      F.wordS (V i) * E i j * (F.wordT (C.word j) * F.wordS (C.word j')) *
        F.wordT (Q.word j') by simp only [mul_assoc], F.prefixCode_orthogonal C j j',
      if_neg (Ne.symm hj'), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Reshaping**: a code pencil over `(R, C)` is carried to one over `(P, Q)` with the same
entries, and the two units are congruent modulo `centralClassGroup`. -/
theorem exists_reshaped_pencil [Nontrivial A] [Nontrivial ι] {k : Type*} [Field k]
    [Algebra k A] (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (R P : AryPrefixCode ρ ι) (hR : F.IsComplete R) (hP : F.IsComplete P)
    (C Q : AryPrefixCode κ ι) (hC : F.IsComplete C) (hQ : F.IsComplete Q)
    (E : ρ → κ → A) (u : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)) :
    ∃ v : Aˣ, (v : A) = ∑ i, ∑ j, F.wordS (P.word i) * E i j * F.wordT (Q.word j) ∧
      (u ∈ centralClassGroup A ↔ v ∈ centralClassGroup A) := by
  set ω₁ : Aˣ := F.codeChangeUnit P R hP hR
  set ω₂ : Aˣ := F.codeChangeUnit C Q hC hQ
  have h₁ : ω₁ ∈ centralClassGroup A :=
    F.codeChange_mem_centralClassGroup (k := k) hdiv _ rfl P R hP hR ω₁ rfl
  have h₂ : ω₂ ∈ centralClassGroup A :=
    F.codeChange_mem_centralClassGroup (k := k) hdiv _ rfl C Q hC hQ ω₂ rfl
  refine ⟨ω₁ * u * ω₂, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hu]
    show (∑ i, F.wordS (P.word i) * F.wordT (R.word i)) *
        (∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
        (∑ j, F.wordS (C.word j) * F.wordT (Q.word j)) = _
    rw [F.codeChange_mul_codePencil P R C.word E,
      F.codePencil_mul_codeChange P.word C Q E]
  · constructor
    · intro h
      exact mul_mem (mul_mem h₁ h) h₂
    · intro h
      have hu' : u = ω₁⁻¹ * (ω₁ * u * ω₂) * ω₂⁻¹ := by group
      rw [hu']
      exact mul_mem (mul_mem (inv_mem h₁) h) (inv_mem h₂)

section Window

variable {k : Type*} [Field k] [Algebra k A]

/-- **The value window of a code pencil**: entry windows shift by row length minus column
length. -/
theorem pencilVal_window_mem {ρ κ : Type*} [Fintype ρ] [Fintype κ] {a b lo hi : ℤ}
    (V : ρ → List ι) (W : κ → List ι) (E : ρ → κ → A)
    (hE : ∀ i j, E i j ∈ Submodule.span k (F.degreeMonomials a b))
    (hlo : ∀ i j, lo ≤ ((V i).length : ℤ) + a - (W j).length)
    (hhi : ∀ i j, ((V i).length : ℤ) + b - (W j).length ≤ hi) :
    (∑ i, ∑ j, F.wordS (V i) * E i j * F.wordT (W j)) ∈
      Submodule.span k (F.degreeMonomials lo hi) := by
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
  have hS : F.wordS (V i) ∈ Submodule.span k
      (F.degreeMonomials ((V i).length : ℤ) ((V i).length : ℤ)) :=
    Submodule.subset_span ⟨V i, [], by simp, by simp, by simp⟩
  have hT : F.wordT (W j) ∈ Submodule.span k
      (F.degreeMonomials (-((W j).length : ℤ)) (-((W j).length : ℤ))) :=
    Submodule.subset_span ⟨[], W j, by simp, by simp, by simp⟩
  have h1 := F.window_mul_mem_span (F.window_mul_mem_span hS (hE i j)) hT
  refine F.span_degreeMonomials_mono ?_ ?_ h1
  · have := hlo i j
    omega
  · have := hhi i j
    omega

end Window

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.codeChange_mul_eq_one
#audit_axioms GroupApproximation.CompleteMatrixFamily.codeChange_mul_codePencil
#audit_axioms GroupApproximation.CompleteMatrixFamily.codePencil_mul_codeChange
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_reshaped_pencil
#audit_axioms GroupApproximation.CompleteMatrixFamily.pencilVal_window_mem
