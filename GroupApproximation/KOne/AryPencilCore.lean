import GroupApproximation.Leavitt.AryLeavittBasis
import GroupApproximation.Meta.AxiomGuard

/-!
# Pencil core at arbitrary arity: the two move generators

`KOne/PencilCore.lean` isolates the two kinds of multiplier the pencil
elimination uses, over a **binary** Leavitt family:

* **scalar-matrix moves** --- the depth-`n` embedding of a matrix over the
  ground field;
* **block unipotents** `1 + N` with `N` supported on `S × T` for disjoint sets
  of depth-`n` words.

This module is the same over a `CompleteMatrixFamily A ι`, together with the
incomparable-unipotent calculus of `KOne/IncomparableUnipotents.lean` that it
rests on.  Both of those files are pure word calculus with `List (Fin 2)` in the
statements, so the port is a substitution.

## The one real change: where the scalar moves land

The binary file concludes `u ∈ stableUnits A` for a scalar move, through
`LeavittBalancedUnits.mem_stableUnits_of_val_mem_levelSpan`.  **That statement
is false at arity `d ≥ 3.**  It rests on `centralClassGroup_le_stableUnits`,
whose binary proof writes a central unit as a product of *two* corner insertions
and concludes `[c] = [c]²`; at arity `d` the same argument gives only
`[c]^{d-1} = 1`, which is `AlgebraicK.kappa_central_pow_card_sub_one` and is
exactly why `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` is nontrivial.

So the scalar moves land in `centralClassGroup` here, not in `stableUnits`, via
`AryDegreeZeroUnits.mem_centralClassGroup_of_val_mem_levelSpan`.  The block
unipotents still land in `stableUnits`, which is contained in
`centralClassGroup`, so the receptacle for the whole elimination at arity `d` is
`centralClassGroup` --- which is what `MatrixDiagonalization.ScalarReduction`
means anyway, so nothing is lost.

## What replaces the prefix code

The binary file indexes depth-`n` words by `fullBinaryCode n` and uses
`prefixCode_orthogonal`.  Here the words of length `n` are indexed by
`Fin n → ι` directly and orthogonality is
`CompleteMatrixFamily.powerFamily_orthogonal`; the scalar embedding is
`(F.powerFamily n).matrixEmbedding`, a ring homomorphism, which also makes the
scalar-move algebra free.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Distinct words of equal length are incomparable -/

theorem ofFn_not_prefix_of_ne {α : Type*} {n : ℕ} {f g : Fin n → α}
    (hfg : f ≠ g) : ¬ List.ofFn f <+: List.ofFn g := by
  intro hp
  exact hfg (List.ofFn_inj.mp (hp.eq_of_length (by simp)))

variable (F : CompleteMatrixFamily A ι)

/-! ### Incomparable unipotents -/

/-- **Incomparable unipotents die**: for prefix-incomparable `a, b`, any unit of
value `1 + s_a·y·t_b` lies in the stably elementary subgroup. -/
theorem incomparable_unipotent_mem_stableUnits {a b : List ι}
    (hab : ¬a <+: b) (hba : ¬b <+: a) (y : A) (u : Aˣ)
    (hu : (u : A) = 1 + F.wordS a * y * F.wordT b) :
    u ∈ stableUnits A := by
  refine mem_stableUnits_of_val_unipotent (F.wordS a * y) (F.wordT b)
    ?_ (by rw [hu])
  rw [show F.wordT b * (F.wordS a * y) = (F.wordT b * F.wordS a) * y from by
    noncomm_ring, F.wordT_mul_wordS_of_incomparable b a hba hab, zero_mul]

/-- The unipotent `1 + s_a y t_b` is a genuine unit, with inverse
`1 - s_a y t_b`. -/
def incomparableUnit {a b : List ι} (hab : ¬a <+: b) (hba : ¬b <+: a)
    (y : A) : Aˣ where
  val := 1 + F.wordS a * y * F.wordT b
  inv := 1 - F.wordS a * y * F.wordT b
  val_inv := by
    have hz : F.wordS a * y * F.wordT b * (F.wordS a * y * F.wordT b) = 0 := by
      rw [show F.wordS a * y * F.wordT b * (F.wordS a * y * F.wordT b) =
        F.wordS a * y * (F.wordT b * F.wordS a) * (y * F.wordT b) from by
          noncomm_ring, F.wordT_mul_wordS_of_incomparable b a hba hab]
      noncomm_ring
    calc (1 + F.wordS a * y * F.wordT b) * (1 - F.wordS a * y * F.wordT b)
        = 1 - F.wordS a * y * F.wordT b *
            (F.wordS a * y * F.wordT b) := by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]
  inv_val := by
    have hz : F.wordS a * y * F.wordT b * (F.wordS a * y * F.wordT b) = 0 := by
      rw [show F.wordS a * y * F.wordT b * (F.wordS a * y * F.wordT b) =
        F.wordS a * y * (F.wordT b * F.wordS a) * (y * F.wordT b) from by
          noncomm_ring, F.wordT_mul_wordS_of_incomparable b a hba hab]
      noncomm_ring
    calc (1 - F.wordS a * y * F.wordT b) * (1 + F.wordS a * y * F.wordT b)
        = 1 - F.wordS a * y * F.wordT b *
            (F.wordS a * y * F.wordT b) := by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]

@[simp] theorem incomparableUnit_val {a b : List ι} (hab : ¬a <+: b)
    (hba : ¬b <+: a) (y : A) :
    ((F.incomparableUnit hab hba y : Aˣ) : A) =
      1 + F.wordS a * y * F.wordT b := rfl

theorem incomparableUnit_mem {a b : List ι} (hab : ¬a <+: b)
    (hba : ¬b <+: a) (y : A) :
    F.incomparableUnit hab hba y ∈ stableUnits A :=
  F.incomparable_unipotent_mem_stableUnits hab hba y _ rfl

/-! ### Move generator I: scalar matrices -/

section Scalars

variable {k : Type*} [Field k] [Algebra k A]

/-- The depth-`n` scalar embedding lands in the balanced span. -/
theorem matrixEmbedding_mem_levelSpan (n : ℕ)
    (G : Matrix (Fin n → ι) (Fin n → ι) k) :
    (F.powerFamily n).matrixEmbedding G ∈
      Submodule.span k (F.levelMonomialSet n) := by
  have hterm : ∀ i j : Fin n → ι,
      F.wordS (List.ofFn i) * algebraMap k A (G i j) * F.wordT (List.ofFn j) =
        G i j • (F.wordS (List.ofFn i) * F.wordT (List.ofFn j)) := by
    intro i j
    rw [Algebra.smul_def, ← mul_assoc, Algebra.commutes]
  rw [matrixEmbedding_apply]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ ?_
  rw [show (F.powerFamily n).left i * algebraMap k A (G i j) *
      (F.powerFamily n).right j =
    F.wordS (List.ofFn i) * algebraMap k A (G i j) *
      F.wordT (List.ofFn j) from rfl, hterm i j]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, j, rfl⟩)

/-- **Scalar-matrix moves lie in the central class group**: a unit whose value
is the depth-`n` embedding of a matrix over `k`.

At arity two the binary file concludes membership in `stableUnits`; that
stronger conclusion is unavailable at `d ≥ 3`, because it rests on the collapse
`centralClassGroup ≤ stableUnits`, which needs `K₁ = 0`. -/
theorem matrixEmbedding_unit_mem_centralClassGroup [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (n : ℕ)
    (G : Matrix (Fin n → ι) (Fin n → ι) k) (u : Aˣ)
    (hu : (u : A) = (F.powerFamily n).matrixEmbedding G) :
    u ∈ centralClassGroup A :=
  F.mem_centralClassGroup_of_val_mem_levelSpan hdiv n u
    (by rw [hu]; exact F.matrixEmbedding_mem_levelSpan n G)

end Scalars

/-! ### Move generator II: block unipotents -/

/-- **Block-unipotent moves are stably elementary**: a unit of value
`1 + Σ_{(i,j) ∈ S × T} s_i · N i j · t_j` with `S`, `T` disjoint sets of
depth-`n` words is a product of incomparable unipotents. -/
theorem sum_incomparable_unipotent_mem {n : ℕ}
    {S T : Finset (Fin n → ι)} (hST : Disjoint S T)
    (N : (Fin n → ι) → (Fin n → ι) → A) (u : Aˣ)
    (hu : (u : A) = 1 + ∑ p ∈ S ×ˢ T,
      F.wordS (List.ofFn p.1) * N p.1 p.2 * F.wordT (List.ofFn p.2)) :
    u ∈ stableUnits A := by
  classical
  suffices h : ∀ P : Finset ((Fin n → ι) × (Fin n → ι)),
      P ⊆ S ×ˢ T → ∀ u : Aˣ,
      (u : A) = 1 + ∑ p ∈ P,
        F.wordS (List.ofFn p.1) * N p.1 p.2 * F.wordT (List.ofFn p.2) →
      u ∈ stableUnits A from h _ subset_rfl u hu
  intro P
  induction P using Finset.cons_induction with
  | empty =>
      intro _ u hu
      have hone : u = 1 := Units.ext (by rw [Units.val_one]; simpa using hu)
      rw [hone]
      exact one_mem _
  | cons p P hp ih =>
      intro hPsub u hu
      have hpST : p ∈ S ×ˢ T := hPsub (Finset.mem_cons.mpr (Or.inl rfl))
      have hp1S : p.1 ∈ S := (Finset.mem_product.mp hpST).1
      have hp2T : p.2 ∈ T := (Finset.mem_product.mp hpST).2
      have hp12 : p.1 ≠ p.2 := fun h ↦
        (Finset.disjoint_left.mp hST hp1S) (h ▸ hp2T)
      have hinc : ¬List.ofFn p.1 <+: List.ofFn p.2 :=
        ofFn_not_prefix_of_ne hp12
      have hinc' : ¬List.ofFn p.2 <+: List.ofFn p.1 :=
        ofFn_not_prefix_of_ne (Ne.symm hp12)
      set ν : Aˣ := F.incomparableUnit hinc hinc' (N p.1 p.2) with hν
      have hνval : (ν : A) = 1 +
          F.wordS (List.ofFn p.1) * N p.1 p.2 * F.wordT (List.ofFn p.2) := rfl
      have hcross : (∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
            F.wordT (List.ofFn q.2)) *
          (F.wordS (List.ofFn p.1) * N p.1 p.2 *
            F.wordT (List.ofFn p.2)) = 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero fun q hq ↦ ?_
        have hqST : q ∈ S ×ˢ T := hPsub (Finset.subset_cons hp hq)
        have hq2T : q.2 ∈ T := (Finset.mem_product.mp hqST).2
        have hne : q.2 ≠ p.1 := fun h ↦
          (Finset.disjoint_left.mp hST hp1S) (h ▸ hq2T)
        have horth : F.wordT (List.ofFn q.2) * F.wordS (List.ofFn p.1) = 0 := by
          have h := F.powerFamily_orthogonal n q.2 p.1
          rw [if_neg hne] at h
          exact h
        rw [show F.wordS (List.ofFn q.1) * N q.1 q.2 *
            F.wordT (List.ofFn q.2) *
            (F.wordS (List.ofFn p.1) * N p.1 p.2 *
              F.wordT (List.ofFn p.2)) =
          F.wordS (List.ofFn q.1) * N q.1 q.2 *
            (F.wordT (List.ofFn q.2) * F.wordS (List.ofFn p.1)) *
            (N p.1 p.2 * F.wordT (List.ofFn p.2)) from by noncomm_ring,
          horth, mul_zero, zero_mul]
      have hval : (1 + ∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
          F.wordT (List.ofFn q.2)) * (ν : A) = (u : A) := by
        rw [hνval, hu, Finset.sum_cons]
        calc (1 + ∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
              F.wordT (List.ofFn q.2)) *
            (1 + F.wordS (List.ofFn p.1) * N p.1 p.2 *
              F.wordT (List.ofFn p.2))
            = 1 + (F.wordS (List.ofFn p.1) * N p.1 p.2 *
                F.wordT (List.ofFn p.2) +
              ∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
                F.wordT (List.ofFn q.2)) +
              (∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
                F.wordT (List.ofFn q.2)) *
              (F.wordS (List.ofFn p.1) * N p.1 p.2 *
                F.wordT (List.ofFn p.2)) := by noncomm_ring
          _ = 1 + (F.wordS (List.ofFn p.1) * N p.1 p.2 *
                F.wordT (List.ofFn p.2) +
              ∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
                F.wordT (List.ofFn q.2)) := by rw [hcross, add_zero]
      have hu' : ((u * ν⁻¹ : Aˣ) : A) = 1 +
          ∑ q ∈ P, F.wordS (List.ofFn q.1) * N q.1 q.2 *
            F.wordT (List.ofFn q.2) := by
        rw [Units.val_mul, ← hval, mul_assoc, Units.mul_inv, mul_one]
      have hsplit : u = (u * ν⁻¹) * ν := by group
      rw [hsplit]
      exact mul_mem
        (ih (fun q hq ↦ hPsub (Finset.subset_cons hp hq)) (u * ν⁻¹) hu')
        (F.incomparableUnit_mem hinc hinc' (N p.1 p.2))

/-- Nested-sum form of the block-unipotent membership. -/
theorem sum_incomparable_unipotent_mem' {n : ℕ}
    {S T : Finset (Fin n → ι)} (hST : Disjoint S T)
    (N : (Fin n → ι) → (Fin n → ι) → A) (u : Aˣ)
    (hu : (u : A) = 1 + ∑ i ∈ S, ∑ j ∈ T,
      F.wordS (List.ofFn i) * N i j * F.wordT (List.ofFn j)) :
    u ∈ stableUnits A := by
  refine F.sum_incomparable_unipotent_mem hST N u ?_
  rw [hu, Finset.sum_product]

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.incomparableUnit_mem
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.matrixEmbedding_unit_mem_centralClassGroup
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.sum_incomparable_unipotent_mem
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.sum_incomparable_unipotent_mem'
