import GroupApproximation.Leavitt.AryWords
import GroupApproximation.Leavitt.AryDivision
import GroupApproximation.KOne.FieldMatrixReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree-zero units at arbitrary arity

`Leavitt/LeavittDegreeZero.lean` proves the degree-zero half of the rose-graph
`K₁` computation for a **binary** Leavitt family: a unit whose value lies in the
span of the balanced monomials `s_α t_β` with `|α| = |β| = n` is a central
scalar modulo the stably elementary units.  Its route is the full binary code at
depth `n`, which identifies the algebra with a `2ⁿ × 2ⁿ` matrix ring.

This module is the same statement over a `CompleteMatrixFamily A ι`, so it
applies to `L_k(1,d)` for every `d`.  Nothing downstream had to be
generalised: `CompleteMatrixFamily.unitsEquiv_field_matrix_mem_centralClassGroup`
of `KOne/FieldMatrixReduction.lean` is already stated for an arbitrary family.

## What replaces the prefix code

The binary file builds `fullBinaryCode n : BinaryPrefixCode (Fin n → Fin 2)` and
turns it into a matrix family.  Prefix codes are not needed: the words of length
`n` are already indexed by `Fin n → ι`, and `powerFamily F n` assembles them
into a `CompleteMatrixFamily A (Fin n → ι)` directly from the two fields of `F`.

* orthogonality is the equal-length case: distinct words of the same length are
  incomparable, so `t_γ s_δ` is `1` on the diagonal and `0` off it;
* completeness is `∑_f s_f t_f = 1`, which `Leavitt/AryKillWord.lean` already
  proves as `CompleteMatrixFamily.sum_cylinder_ofFn`.

## Where this sits in the `ScalarReduction` chain

`MatrixDiagonalization.ScalarReduction (L_k(1,d))` --- every unit is a central
unit times a stably elementary one --- is, after
`KOne/AryCentralUnitsAreScalars.lean`, the single remaining input of the printed
`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`.  It splits the way the binary development
splits it:

* **degree zero**, a unit already balanced at some depth: this file, at every
  arity;
* **width reduction**, moving an arbitrary unit into a bounded degree window
  modulo the central class group: `Leavitt/BinaryLeavittWindow.lean` and the
  `KOne/` pencil development, still binary only.

So this closes the first half at arity `d` and leaves the second, which is where
the `d = 2` route uses `K₁(L_k(1,2)) = 0` and does not transfer.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open scoped BigOperators

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-! ### The depth-`n` power family -/

/-- **The depth-`n` power family**: the words of length `n` form a complete
matrix family indexed by `Fin n → ι`, so `A ≅ M_{ιⁿ}(A)`. -/
def powerFamily (n : ℕ) : CompleteMatrixFamily A (Fin n → ι) where
  left f := F.wordS (List.ofFn f)
  right g := F.wordT (List.ofFn g)
  orthogonal g f := by
    rcases eq_or_ne g f with rfl | hgf
    · rw [if_pos rfl]
      exact F.wordT_mul_wordS_self _
    · rw [if_neg hgf]
      refine F.wordT_mul_wordS_of_incomparable _ _ ?_ ?_
      · intro hp
        exact hgf (List.ofFn_inj.mp (hp.eq_of_length (by simp)))
      · intro hp
        exact hgf (List.ofFn_inj.mp (hp.eq_of_length (by simp))).symm
  complete := F.sum_cylinder_ofFn n

@[simp] theorem powerFamily_left (n : ℕ) (f : Fin n → ι) :
    (F.powerFamily n).left f = F.wordS (List.ofFn f) := rfl

@[simp] theorem powerFamily_right (n : ℕ) (g : Fin n → ι) :
    (F.powerFamily n).right g = F.wordT (List.ofFn g) := rfl

theorem powerFamily_orthogonal (n : ℕ) (a b : Fin n → ι) :
    F.wordT (List.ofFn a) * F.wordS (List.ofFn b) = if a = b then 1 else 0 :=
  (F.powerFamily n).orthogonal a b

/-! ### Balanced monomials -/

/-- The balanced (degree-zero) monomials at depth `n`. -/
def levelMonomialSet (n : ℕ) : Set A :=
  {x | ∃ f g : Fin n → ι,
    x = F.wordS (List.ofFn f) * F.wordT (List.ofFn g)}

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Matrix entries of degree-zero elements are scalars: compressing an element
of the balanced span between equal-length words lands in the image of the ground
ring. -/
theorem entry_mem_range_algebraMap (n : ℕ) {x : A}
    (hx : x ∈ Submodule.span k (F.levelMonomialSet n))
    (γ δ : Fin n → ι) :
    F.wordT (List.ofFn γ) * x * F.wordS (List.ofFn δ) ∈
      Set.range (algebraMap k A) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨f, g, rfl⟩ := hxmem
      rw [show F.wordT (List.ofFn γ) *
          (F.wordS (List.ofFn f) * F.wordT (List.ofFn g)) *
          F.wordS (List.ofFn δ) =
        (F.wordT (List.ofFn γ) * F.wordS (List.ofFn f)) *
          (F.wordT (List.ofFn g) * F.wordS (List.ofFn δ)) from by
            noncomm_ring,
        F.powerFamily_orthogonal n γ f, F.powerFamily_orthogonal n g δ]
      refine ⟨(if γ = f then 1 else 0) * (if g = δ then 1 else 0), ?_⟩
      rw [map_mul]
      congr 1 <;> split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨cx, hcx⟩ := hx
      obtain ⟨cy, hcy⟩ := hy
      exact ⟨cx + cy, by rw [map_add, hcx, hcy]; noncomm_ring⟩
  | smul r x _ hx =>
      obtain ⟨c, hc⟩ := hx
      refine ⟨r * c, ?_⟩
      rw [map_mul, hc, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

end Scalars

/-! ### The degree-zero reduction -/

section Reduction

open MatrixDiagonalization

variable {k : Type*} [Field k] [Algebra k A]

/-- **Degree-zero scalar reduction at arbitrary arity**: a unit whose value lies
in the balanced span at some depth is a central scalar modulo the stably
elementary units. -/
theorem mem_centralClassGroup_of_val_mem_levelSpan [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (n : ℕ) (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (F.levelMonomialSet n)) :
    u ∈ centralClassGroup A := by
  classical
  have hentry : ∀ γ δ : Fin n → ι, ∃ c : k,
      algebraMap k A c =
        (F.powerFamily n).right γ * (u : A) * (F.powerFamily n).left δ := by
    intro γ δ
    obtain ⟨c, hc⟩ := F.entry_mem_range_algebraMap (k := k) n hu γ δ
    exact ⟨c, hc⟩
  choose C hC using hentry
  have hU : (((F.powerFamily n).unitsEquiv.symm u :
        (Matrix (Fin n → ι) (Fin n → ι) A)ˣ) :
        Matrix (Fin n → ι) (Fin n → ι) A) =
      (algebraMap k A).mapMatrix (Matrix.of C) := by
    have hval : (((F.powerFamily n).unitsEquiv.symm u :
          (Matrix (Fin n → ι) (Fin n → ι) A)ˣ) :
          Matrix (Fin n → ι) (Fin n → ι) A) =
        (F.powerFamily n).matrixRingEquiv.symm ((u : Aˣ) : A) := rfl
    rw [hval]
    ext γ δ
    rw [(F.powerFamily n).matrixRingEquiv_symm_apply]
    exact (hC γ δ).symm
  have hmem := (F.powerFamily n).unitsEquiv_field_matrix_mem_centralClassGroup
    hdiv (algebraMap k A) (fun r x ↦ Algebra.commutes r x) (Matrix.of C)
    ((F.powerFamily n).unitsEquiv.symm u) hU
  rwa [MulEquiv.apply_symm_apply] at hmem

end Reduction

end CompleteMatrixFamily

/-! ### The Leavitt specialisation -/

namespace AryLeavitt

open MatrixDiagonalization

/-- **A balanced unit of `L_k(1,d)` is a scalar modulo the stably elementary
units**, for every field `k` and every `d ≥ 2`.

This is the degree-zero half of the rose-graph input
`MatrixDiagonalization.ScalarReduction (L_k(1,d))`, at every arity.  The other
half --- moving an arbitrary unit into a bounded degree window --- is not proved
here at any arity beyond two. -/
theorem mem_centralClassGroup_of_val_mem_levelSpan
    (k : Type) [Field k] (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (u : (AryLeavittAlgebra k d)ˣ)
    (hu : ((u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).levelMonomialSet n)) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  haveI : NeZero d := ⟨by omega⟩
  exact (family k d).mem_centralClassGroup_of_val_mem_levelSpan
    (fun x hx ↦ exists_mul_mul_eq_one k d hd hx) n u hu

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.powerFamily_orthogonal
#audit_axioms GroupApproximation.CompleteMatrixFamily.entry_mem_range_algebraMap
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.mem_centralClassGroup_of_val_mem_levelSpan
#audit_axioms GroupApproximation.AryLeavitt.mem_centralClassGroup_of_val_mem_levelSpan
