import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Words
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner `M_S(F_2) ↪ C_2` and the block embedding `GL_{ι × S}(F_2) → GL_ι(C_2)`

Lane `sk-leavitt-19`, second module.

For a finite set `S` of words, the matrix units `u(α, β) = α p β*` (`α, β ∈ S`)
give a non-unital ring homomorphism `corner : M_S(F_2) → R`,
`M ↦ Σ M_{αβ} u(α, β)` (`cornerHom`).  It is injective as soon as `p ≠ 0`:
the coefficient `M_{αβ}` is recovered by `p α* (corner M) β p = M_{αβ} p`
(`extract_corner`).  Entrywise this gives `block : M_{ι × S}(F_2) → M_ι(R)`,
and `B ↦ 1 - block 1 + block B` is a monoid homomorphism (`glMap`): this is the
local-unit corner `e M e` of the excision argument, with `e = block 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

namespace CohnTwoData

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R] (C : CohnTwoData R)
  (S : Finset (List (Fin 2)))

/-- `corner M = Σ_{α, β ∈ S} M_{αβ} • α p β*`. -/
def corner (M : Matrix S S (ZMod 2)) : R :=
  ∑ α : S, ∑ β : S, M α β • C.unit (α : List (Fin 2)) (β : List (Fin 2))

theorem corner_zero : C.corner S 0 = 0 := by
  simp only [corner, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

theorem corner_add (M N : Matrix S S (ZMod 2)) :
    C.corner S (M + N) = C.corner S M + C.corner S N := by
  simp only [corner, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem corner_sub (M N : Matrix S S (ZMod 2)) :
    C.corner S (M - N) = C.corner S M - C.corner S N := by
  simp only [corner, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem corner_single (α β : S) (c : ZMod 2) :
    C.corner S (Matrix.single α β c) = c • C.unit (α : List (Fin 2)) (β : List (Fin 2)) := by
  rw [corner, Finset.sum_eq_single α, Finset.sum_eq_single β, Matrix.single_apply_same]
  · intro β' _ hβ'
    rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hβ'), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ β) h
  · intro α' _ hα'
    refine Finset.sum_eq_zero fun β' _ ↦ ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm hα'), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ α) h

theorem corner_mul (M N : Matrix S S (ZMod 2)) :
    C.corner S (M * N) = C.corner S M * C.corner S N := by
  induction M using Matrix.induction_on' with
  | h_zero => rw [Matrix.zero_mul, corner_zero, zero_mul]
  | h_add P Q hP hQ => rw [add_mul, corner_add, corner_add, hP, hQ, add_mul]
  | h_std_basis α β c =>
    induction N using Matrix.induction_on' with
    | h_zero => rw [Matrix.mul_zero, corner_zero, mul_zero]
    | h_add P Q hP hQ => rw [mul_add, corner_add, corner_add, hP, hQ, mul_add]
    | h_std_basis γ δ d =>
      rw [corner_single, corner_single, smul_mul_smul_comm, unit_mul_unit]
      by_cases hβγ : β = γ
      · subst hβγ
        rw [Matrix.single_mul_single_same, corner_single, if_pos rfl]
      · rw [Matrix.single_mul_single_of_ne _ _ _ hβγ, corner_zero,
          if_neg (fun h ↦ hβγ (Subtype.ext h)), smul_zero]

/-- **Coefficient extraction** `p α* (corner M) β p = M_{αβ} • p`. -/
theorem extract_corner (M : Matrix S S (ZMod 2)) (α β : S) :
    C.p * (C.coword (α : List (Fin 2)) * (C.corner S M * (C.word (β : List (Fin 2)) * C.p))) =
      M α β • C.p := by
  induction M using Matrix.induction_on' with
  | h_zero => rw [corner_zero, zero_mul, mul_zero, mul_zero, Matrix.zero_apply, zero_smul]
  | h_add P Q hP hQ =>
    rw [corner_add, add_mul, mul_add, mul_add, hP, hQ, Matrix.add_apply, add_smul]
  | h_std_basis α' β' c =>
    rw [corner_single, smul_mul_assoc, mul_smul_comm, mul_smul_comm, extract]
    by_cases h1 : α' = α
    · subst h1
      by_cases h2 : β' = β
      · subst h2
        rw [if_pos ⟨rfl, rfl⟩, Matrix.single_apply_same]
      · rw [if_neg (fun h ↦ h2 (Subtype.ext h.2)), smul_zero,
          Matrix.single_apply_of_col_ne _ _ h2, zero_smul]
    · rw [if_neg (fun h ↦ h1 (Subtype.ext h.1.symm)), smul_zero,
        Matrix.single_apply_of_row_ne h1, zero_smul]

theorem corner_eq_zero (hp : C.p ≠ 0) (M : Matrix S S (ZMod 2)) (h : C.corner S M = 0) :
    M = 0 := by
  ext α β
  have hx := C.extract_corner S M α β
  rw [h, zero_mul, mul_zero, mul_zero] at hx
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases (M α β) with h0 | h1
  · rw [h0, Matrix.zero_apply]
  · rw [h1, one_smul] at hx
    exact absurd hx.symm hp

theorem corner_injective (hp : C.p ≠ 0) : Function.Injective (C.corner S) := by
  intro M N h
  refine sub_eq_zero.mp (C.corner_eq_zero S hp (M - N) ?_)
  rw [corner_sub, h, sub_self]

/-- `corner` as a non-unital ring homomorphism. -/
def cornerHom : Matrix S S (ZMod 2) →ₙ+* R where
  toFun := C.corner S
  map_mul' := C.corner_mul S
  map_zero' := C.corner_zero S
  map_add' := C.corner_add S

theorem cornerHom_apply (M : Matrix S S (ZMod 2)) : C.cornerHom S M = C.corner S M := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block embedding `M_{ι × S}(F_2) → M_ι(R)`: entry `(i, j)` is the corner
of the `(i, j)` block. -/
def block (B : Matrix (ι × S) (ι × S) (ZMod 2)) : Matrix ι ι R :=
  ((Matrix.comp ι ι S S (ZMod 2)).symm B).map (C.cornerHom S)

theorem block_mul (B B' : Matrix (ι × S) (ι × S) (ZMod 2)) :
    C.block S (B * B') = C.block S B * C.block S B' := by
  simp only [block, ← Matrix.compRingEquiv_symm_apply, map_mul, Matrix.map_mul]

theorem block_add (B B' : Matrix (ι × S) (ι × S) (ZMod 2)) :
    C.block S (B + B') = C.block S B + C.block S B' := by
  rw [block, block, block]
  have hsymm : (Matrix.comp ι ι S S (ZMod 2)).symm (B + B') =
      (Matrix.comp ι ι S S (ZMod 2)).symm B + (Matrix.comp ι ι S S (ZMod 2)).symm B' := rfl
  rw [hsymm, Matrix.map_add _ (map_add (C.cornerHom S))]

theorem block_injective (hp : C.p ≠ 0) : Function.Injective (C.block (ι := ι) S) := by
  intro B B' h
  refine (Matrix.comp ι ι S S (ZMod 2)).symm.injective (Matrix.ext fun i j ↦ ?_)
  have hij : C.cornerHom S ((Matrix.comp ι ι S S (ZMod 2)).symm B i j) =
      C.cornerHom S ((Matrix.comp ι ι S S (ZMod 2)).symm B' i j) := by
    simpa only [block, Matrix.map_apply] using congrFun (congrFun h i) j
  rw [cornerHom_apply, cornerHom_apply] at hij
  exact C.corner_injective S hp hij

/-- The corner monoid homomorphism `B ↦ 1 - block 1 + block B`. -/
def glMap : Matrix (ι × S) (ι × S) (ZMod 2) →* Matrix ι ι R where
  toFun B := 1 - C.block S 1 + C.block S B
  map_one' := sub_add_cancel _ _
  map_mul' B B' := by
    have hQQ : C.block S 1 * C.block (ι := ι) S 1 = C.block S 1 := by
      rw [← C.block_mul, mul_one]
    have hQY : C.block S 1 * C.block S B' = C.block S B' := by
      rw [← C.block_mul, one_mul]
    have hXQ : C.block S B * C.block S 1 = C.block S B := by
      rw [← C.block_mul, mul_one]
    have expand : ∀ Q X Y : Matrix ι ι R, (1 - Q + X) * (1 - Q + Y) =
        (1 - Q + X * Y) + (Q * Q - Q) + (Y - Q * Y) + (X - X * Q) := by
      intro Q X Y
      noncomm_ring
    show 1 - C.block S 1 + C.block S (B * B') =
      (1 - C.block S 1 + C.block S B) * (1 - C.block S 1 + C.block S B')
    rw [C.block_mul, expand, hQQ, hQY, hXQ, sub_self, sub_self, sub_self, add_zero, add_zero,
      add_zero]

theorem glMap_apply (B : Matrix (ι × S) (ι × S) (ZMod 2)) :
    C.glMap S B = 1 - C.block S 1 + C.block S B := rfl

theorem glMap_one_add (A : Matrix (ι × S) (ι × S) (ZMod 2)) :
    C.glMap S (1 + A) = 1 + C.block S A := by
  rw [glMap_apply, block_add, ← add_assoc, sub_add_cancel]

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.corner_mul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.corner_injective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.block_injective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.glMap_one_add
