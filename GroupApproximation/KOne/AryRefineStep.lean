import GroupApproximation.KOne.AryPencilCodeMoves
import GroupApproximation.Meta.AxiomGuard

/-!
# The refinement step, at arbitrary arity

`KOne/RefineStep.lean` over a complete matrix family on an alphabet `ι`.  A pencil column with
no `s`-content splits into its `|ι|` children: the same element, over the column code with
one word replaced by its one-letter extensions, carries pencil data in which the split
column's `t`-coefficients descend to constants and its constant coefficient to
`s`-coefficients.  The binary identity `pE(a₀,a₁,c,0,0)·s_z` has one pencil entry per letter;
at arity `d` it is `pE(a, 0, c)·s_z = pE(0, c·e_z, a_z)`.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

/-- The split entry identity: an `s`-free pencil entry times `s_z` is again a pencil entry,
with the `t`-coefficient of `z` descending to the constant and the constant ascending to the
`s`-coefficient of `z`. -/
theorem pencilEntry_zero_mul_left (a : ι → k) (c : k) (z : ι) :
    F.pencilEntry a (fun _ ↦ 0) c * F.left z =
      F.pencilEntry (fun _ ↦ 0) (fun w ↦ if w = z then c else 0) (a z) := by
  classical
  have h1 : (∑ w, a w • F.right w) * F.left z = a z • (1 : A) := by
    rw [Finset.sum_mul, Finset.sum_eq_single z]
    · rw [smul_mul_assoc, F.orthogonal, if_pos rfl]
    · intro w _ hw
      rw [smul_mul_assoc, F.orthogonal, if_neg hw, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ z) h
  have h2 : (∑ w, (if w = z then c else 0) • F.left w) = c • F.left z := by
    rw [Finset.sum_eq_single z]
    · rw [if_pos rfl]
    · intro w _ hw
      rw [if_neg hw, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ z) h
  unfold pencilEntry
  simp only [zero_smul, Finset.sum_const_zero, add_zero, zero_add]
  rw [add_mul, h1, h2, smul_mul_assoc, one_mul]

/-- **The refinement step**: the pencil value over `(R, C)` with an `s`-free column `j₀`
equals the pencil value over the column code split at `j₀`, indexed by
`ι ⊕ {j // j ≠ j₀}`, with the shifted data on the children. -/
theorem refine_column {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (C : AryPrefixCode κ ι) (Ac Bc : ρ → κ → ι → k)
    (Cm : ρ → κ → k) (j₀ : κ) (hB : ∀ i, Bc i j₀ = fun _ ↦ 0) :
    (∑ i, ∑ j, F.wordS (R.word i) * F.pencilEntry (Ac i j) (Bc i j) (Cm i j) *
      F.wordT (C.word j)) =
    ∑ i, ∑ p : ι ⊕ {j : κ // j ≠ j₀}, F.wordS (R.word i) *
      Sum.elim
        (fun z ↦ F.pencilEntry (fun _ ↦ 0) (fun w ↦ if w = z then Cm i j₀ else 0)
          (Ac i j₀ z))
        (fun q ↦ F.pencilEntry (Ac i q.1) (Bc i q.1) (Cm i q.1)) p *
      F.wordT (Sum.elim (fun z ↦ C.word j₀ ++ [z]) (fun q ↦ C.word q.1) p) := by
  classical
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.add_sum_erase _ (fun j ↦ F.wordS (R.word i) *
      F.pencilEntry (Ac i j) (Bc i j) (Cm i j) * F.wordT (C.word j)) (Finset.mem_univ j₀),
    Fintype.sum_sum_type]
  have hsplit : F.wordS (R.word i) * F.pencilEntry (Ac i j₀) (Bc i j₀) (Cm i j₀) *
      F.wordT (C.word j₀) =
      ∑ z : ι, F.wordS (R.word i) *
        F.pencilEntry (fun _ ↦ 0) (fun w ↦ if w = z then Cm i j₀ else 0) (Ac i j₀ z) *
        F.wordT (C.word j₀ ++ [z]) := by
    have hT : ∀ z : ι, F.wordT (C.word j₀ ++ [z]) = F.right z * F.wordT (C.word j₀) := by
      intro z
      rw [wordT_append, wordT_singleton]
    simp only [hT, hB i]
    rw [show F.wordS (R.word i) * F.pencilEntry (Ac i j₀) (fun _ ↦ 0) (Cm i j₀) *
          F.wordT (C.word j₀) =
        F.wordS (R.word i) *
          (F.pencilEntry (Ac i j₀) (fun _ ↦ 0) (Cm i j₀) * ∑ z, F.left z * F.right z) *
          F.wordT (C.word j₀) from by rw [F.complete, mul_one],
      Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [← F.pencilEntry_zero_mul_left (Ac i j₀) (Cm i j₀) z]
    noncomm_ring
  rw [hsplit]
  congr 1
  refine (Finset.sum_bij' (i := fun (q : {j : κ // j ≠ j₀}) _ ↦ q.1)
    (j := fun j hj ↦ (⟨j, (Finset.mem_erase.mp hj).1⟩ : {j : κ // j ≠ j₀}))
    ?_ ?_ ?_ ?_ ?_).symm
  · intro q _
    exact Finset.mem_erase.mpr ⟨q.2, Finset.mem_univ _⟩
  · intro j _
    exact Finset.mem_univ _
  · intro q _
    rfl
  · intro j _
    rfl
  · intro q _
    rfl

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.pencilEntry_zero_mul_left
#audit_axioms GroupApproximation.CompleteMatrixFamily.refine_column
