import GroupApproximation.KOne.AryGradedComponents
import GroupApproximation.KOne.AryShapeCalculus
import GroupApproximation.KOne.AryPencilEntry
import GroupApproximation.Meta.AxiomGuard

/-!
# The pencil form, at arbitrary arity

`KOne/PencilForm.lean` over a complete matrix family on an alphabet `ι`: every element of
the degree window `[-1, 1]` is, at some depth `m`, a word-indexed matrix of pencil entries
`∑ᵣ aᵣ tᵣ + c + ∑ᵣ bᵣ sᵣ` with scalar coefficients.  The binary file builds the three
coefficient matrices from balanced embeddings; here they come from the shape calculus.  The
degree `-1` component is shape `(m, m+1)`, and compressing it between depth-`m` words pops
the last column letter out as `tᵣ` (`wordT_mul_wordS_of_shapeRep_right`); the degree `+1`
component pops the last row letter out as `sᵣ` (`wordT_mul_wordS_of_shapeRep_left`).
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

theorem ofFn_snoc_eq_append {m : ℕ} (f : Fin m → ι) (r : ι) :
    List.ofFn (Fin.snoc f r : Fin (m + 1) → ι) = List.ofFn f ++ [r] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

/-- Compressing a shape-`(p, q+1)` element between words of lengths `p` and `q` pops the
last column letter out as a `t`-generator. -/
theorem wordT_mul_wordS_of_shapeRep_right {p q : ℕ}
    {M : Matrix (Fin p → ι) (Fin (q + 1) → ι) k} {y : A} (h : F.ShapeRep p (q + 1) M y)
    (γ : Fin p → ι) (δ : Fin q → ι) :
    F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ) =
      ∑ r, M γ (Fin.snoc δ r) • F.right r := by
  calc F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ)
      = F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ) * ∑ r, F.left r * F.right r := by
        rw [F.complete, mul_one]
    _ = ∑ r, F.wordT (List.ofFn γ) * y *
          F.wordS (List.ofFn (Fin.snoc δ r : Fin (q + 1) → ι)) * F.right r := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [ofFn_snoc_eq_append, wordS_append, wordS_singleton]
        simp only [mul_assoc]
    _ = ∑ r, M γ (Fin.snoc δ r) • F.right r := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [F.shapeRep_entry h, ← Algebra.smul_def]

/-- Compressing a shape-`(p+1, q)` element between words of lengths `p` and `q` pops the
last row letter out as an `s`-generator. -/
theorem wordT_mul_wordS_of_shapeRep_left {p q : ℕ}
    {M : Matrix (Fin (p + 1) → ι) (Fin q → ι) k} {y : A} (h : F.ShapeRep (p + 1) q M y)
    (γ : Fin p → ι) (δ : Fin q → ι) :
    F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ) =
      ∑ r, M (Fin.snoc γ r) δ • F.left r := by
  calc F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ)
      = (∑ r, F.left r * F.right r) * (F.wordT (List.ofFn γ) * y * F.wordS (List.ofFn δ)) := by
        rw [F.complete, one_mul]
    _ = ∑ r, F.left r * (F.wordT (List.ofFn (Fin.snoc γ r : Fin (p + 1) → ι)) * y *
          F.wordS (List.ofFn δ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [ofFn_snoc_eq_append, wordT_append, wordT_singleton]
        simp only [mul_assoc]
    _ = ∑ r, M (Fin.snoc γ r) δ • F.left r := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [F.shapeRep_entry h, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The scalar-pencil form**: every element of the window `[-1, 1]` is, at some depth
`m`, a word-indexed matrix of pencil entries with scalar coefficients. -/
theorem exists_pencil_form {x : A} (hx : x ∈ Submodule.span k (F.degreeMonomials (-1) 1)) :
    ∃ (m : ℕ) (Ac Bc : (Fin m → ι) → (Fin m → ι) → ι → k)
      (Cm : (Fin m → ι) → (Fin m → ι) → k),
      x = ∑ i, ∑ j, F.wordS (List.ofFn i) * F.pencilEntry (Ac i j) (Bc i j) (Cm i j) *
        F.wordT (List.ofFn j) := by
  classical
  obtain ⟨y, hymem, -, hysum⟩ := F.exists_components hx
  have hval : x = y (-1) + y 0 + y 1 := by
    rw [hysum]
    have hIcc : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
      add_assoc]
  obtain ⟨n₁, hn₁⟩ := F.exists_shapeSpan_of_degreeSpan (hymem (-1))
  obtain ⟨n₀, hn₀⟩ := F.exists_shapeSpan_of_degreeSpan (hymem 0)
  obtain ⟨n₂, hn₂⟩ := F.exists_shapeSpan_of_degreeSpan (hymem 1)
  set m : ℕ := n₁ + n₀ + n₂ with hm
  obtain ⟨M₁, hM₁⟩ := F.exists_shapeRep (hn₁ m (m + 1) (by omega) (by omega))
  obtain ⟨M₀, hM₀⟩ := F.exists_shapeRep (hn₀ m m (by omega) (by omega))
  obtain ⟨M₂, hM₂⟩ := F.exists_shapeRep (hn₂ (m + 1) m (by omega) (by omega))
  refine ⟨m, fun i j r ↦ M₁ i (Fin.snoc j r), fun i j r ↦ M₂ (Fin.snoc i r) j,
    fun i j ↦ M₀ i j, ?_⟩
  have hpart : x = ∑ i : Fin m → ι, ∑ j : Fin m → ι,
      F.wordS (List.ofFn i) * (F.wordT (List.ofFn i) * x * F.wordS (List.ofFn j)) *
        F.wordT (List.ofFn j) := by
    calc x = (∑ i : Fin m → ι, F.cylinder (List.ofFn i)) * x *
          (∑ j : Fin m → ι, F.cylinder (List.ofFn j)) := by
          rw [F.sum_cylinder_ofFn m, one_mul, mul_one]
      _ = _ := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [cylinder, mul_assoc]
  rw [hpart]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  congr 1
  rw [hval, mul_add, mul_add, add_mul, add_mul, F.wordT_mul_wordS_of_shapeRep_right hM₁,
    F.shapeRep_entry hM₀, F.wordT_mul_wordS_of_shapeRep_left hM₂,
    Algebra.algebraMap_eq_smul_one]
  rfl

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_mul_wordS_of_shapeRep_right
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_mul_wordS_of_shapeRep_left
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_pencil_form
