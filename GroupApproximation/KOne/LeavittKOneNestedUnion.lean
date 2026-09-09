import GroupApproximation.KOne.LeavittKOneWhitehead
import GroupApproximation.Meta.AxiomGuard

/-!
# Everything finite happens at one stage of a nested union of subrings

For `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` the degree-zero part
`L₀ = ⋃ₙ M_{dⁿ}(k)` has to have its `K₁` computed as the colimit of the
`K₁(M_{dⁿ}(k))`, which `KOne/LeavittKOnePowerColimit.lean` then evaluates.  The
two halves of "`K₁` commutes with a nested union" are both instances of the same
finiteness principle: an invertible matrix has finitely many entries, and an
elementary matrix is built from finitely many generators, so each lives at a
single stage.

This module proves that principle for an arbitrary ring `S` written as a nested
union of subrings `A : ℕ → Subring S`:

* `exists_stage_units` --- an invertible matrix over `S` is the image of an
  invertible matrix over some `A n`.  The entries of the matrix **and of its
  inverse** are finitely many, so one stage holds them all, and invertibility
  descends because the coefficient map is injective.
* `elementaryGroup_le_iSup_map` --- an elementary matrix over `S` lies in the
  join of the images of the `EL_ι(A n)`; on generators this is one choice of
  stage for one entry.
* `elementaryImageStage_mono` and `exists_stage_elementary` --- those images
  increase with `n`, so the join is a union and a single stage suffices.

## What this is and is not

It is the finiteness half of "`K₁` commutes with filtered colimits", stated
without building a second colimit: the two theorems are exactly what a colimit
comparison map needs for surjectivity and for injectivity.  It is **not** the
statement that `L₀` is such a union, which needs `L₀` as a ring, nor the
`K₁(M_n(k)) ≅ k^×` at each stage, which is lane `o-morita`'s
`FieldKOneDeterminant`.

Nothing here mentions the Leavitt algebra.
-/

namespace GroupApproximation
namespace KOneDescent

open AlgebraicK

variable {S : Type*} [Ring S] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Invertible matrices descend to a stage -/

/-- The coefficient map of a subring is injective on matrices. -/
theorem subtype_mapMatrix_injective (A : Subring S) :
    Function.Injective
      (A.subtype.mapMatrix : Matrix ι ι A → Matrix ι ι S) := by
  intro X Y hXY
  ext p q
  exact congrFun (congrFun hXY p) q

/-- **An invertible matrix over a nested union lives at one stage.**  Its
entries and those of its inverse are finitely many, so a single `A n` holds
them all; invertibility descends because the coefficient map is injective. -/
theorem exists_stage_units (A : ℕ → Subring S) (hmono : Monotone A)
    (hcov : ∀ s : S, ∃ n : ℕ, s ∈ A n) (M : (Matrix ι ι S)ˣ) :
    ∃ (n : ℕ) (N : (Matrix ι ι (A n))ˣ),
      elementaryMatrixUnitMap (A n).subtype N = M := by
  classical
  obtain ⟨ν, hν⟩ : ∃ ν : S → ℕ, ∀ s : S, s ∈ A (ν s) :=
    ⟨fun s ↦ (hcov s).choose, fun s ↦ (hcov s).choose_spec⟩
  refine ⟨Finset.univ.sup (fun p : ι × ι ↦
      max (ν ((M : Matrix ι ι S) p.1 p.2))
        (ν ((↑M⁻¹ : Matrix ι ι S) p.1 p.2))), ?_⟩
  set n := Finset.univ.sup (fun p : ι × ι ↦
      max (ν ((M : Matrix ι ι S) p.1 p.2))
        (ν ((↑M⁻¹ : Matrix ι ι S) p.1 p.2))) with hn
  have hMmem : ∀ p q : ι, (M : Matrix ι ι S) p q ∈ A n := by
    intro p q
    refine hmono ?_ (hν _)
    calc ν ((M : Matrix ι ι S) p q)
        ≤ max (ν ((M : Matrix ι ι S) p q))
            (ν ((↑M⁻¹ : Matrix ι ι S) p q)) := le_max_left _ _
      _ ≤ n := Finset.le_sup (f := fun p : ι × ι ↦
            max (ν ((M : Matrix ι ι S) p.1 p.2))
              (ν ((↑M⁻¹ : Matrix ι ι S) p.1 p.2))) (Finset.mem_univ (p, q))
  have hMinvmem : ∀ p q : ι, (↑M⁻¹ : Matrix ι ι S) p q ∈ A n := by
    intro p q
    refine hmono ?_ (hν _)
    calc ν ((↑M⁻¹ : Matrix ι ι S) p q)
        ≤ max (ν ((M : Matrix ι ι S) p q))
            (ν ((↑M⁻¹ : Matrix ι ι S) p q)) := le_max_right _ _
      _ ≤ n := Finset.le_sup (f := fun p : ι × ι ↦
            max (ν ((M : Matrix ι ι S) p.1 p.2))
              (ν ((↑M⁻¹ : Matrix ι ι S) p.1 p.2))) (Finset.mem_univ (p, q))
  set N : Matrix ι ι (A n) :=
    Matrix.of fun p q ↦ (⟨(M : Matrix ι ι S) p q, hMmem p q⟩ : A n) with hNdef
  set N' : Matrix ι ι (A n) :=
    Matrix.of fun p q ↦ (⟨(↑M⁻¹ : Matrix ι ι S) p q, hMinvmem p q⟩ : A n) with hN'def
  have hNval : (A n).subtype.mapMatrix N = (M : Matrix ι ι S) := by
    ext p q
    rfl
  have hN'val : (A n).subtype.mapMatrix N' = (↑M⁻¹ : Matrix ι ι S) := by
    ext p q
    rfl
  have hNN' : N * N' = 1 := by
    refine subtype_mapMatrix_injective (A n) ?_
    rw [map_mul, hNval, hN'val, map_one]
    exact M.val_inv
  have hN'N : N' * N = 1 := by
    refine subtype_mapMatrix_injective (A n) ?_
    rw [map_mul, hNval, hN'val, map_one]
    exact M.inv_val
  refine ⟨⟨N, N', hNN', hN'N⟩, ?_⟩
  apply Units.ext
  exact hNval

/-! ### Elementary matrices descend to a stage -/

/-- **An elementary matrix over a nested union lies in the join of the stage
images.**  On a generator `x_{ij}(a)` this is one choice of stage for `a`. -/
theorem elementaryGroup_le_iSup_map (A : ℕ → Subring S)
    (hcov : ∀ s : S, ∃ n : ℕ, s ∈ A n) :
    elementaryGroup ι S ≤ ⨆ n : ℕ,
      (elementaryGroup ι (A n)).map (elementaryMatrixUnitMap (A n).subtype) := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  obtain ⟨n, hn⟩ := hcov a
  refine Subgroup.mem_iSup_of_mem n ?_
  refine ⟨elementaryUnit i j hij (⟨a, hn⟩ : A n),
    elementaryUnit_mem _ _ _ _, ?_⟩
  rw [elementaryMatrixUnitMap_elementaryUnit]
  rfl

/-- The stage images increase with the stage. -/
theorem elementaryImageStage_mono (A : ℕ → Subring S) (hmono : Monotone A)
    {n m : ℕ} (h : n ≤ m) :
    (elementaryGroup ι (A n)).map (elementaryMatrixUnitMap (A n).subtype)
      ≤ (elementaryGroup ι (A m)).map (elementaryMatrixUnitMap (A m).subtype) := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨elementaryMatrixUnitMap (Subring.inclusion (hmono h)) v, ?_, ?_⟩
  · exact elementaryGroup_map_le _ (Subgroup.mem_map_of_mem _ hv)
  · apply Units.ext
    ext p q
    rfl

/-- **An elementary matrix over a nested union is elementary at one stage.** -/
theorem exists_stage_elementary (A : ℕ → Subring S) (hmono : Monotone A)
    (hcov : ∀ s : S, ∃ n : ℕ, s ∈ A n) {u : (Matrix ι ι S)ˣ}
    (hu : u ∈ elementaryGroup ι S) :
    ∃ n : ℕ, u ∈ (elementaryGroup ι (A n)).map
      (elementaryMatrixUnitMap (A n).subtype) := by
  have hdir : Directed (· ≤ ·) (fun n : ℕ ↦
      (elementaryGroup ι (A n)).map (elementaryMatrixUnitMap (A n).subtype)) :=
    fun n m ↦ ⟨max n m, elementaryImageStage_mono A hmono (le_max_left n m),
      elementaryImageStage_mono A hmono (le_max_right n m)⟩
  exact (Subgroup.mem_iSup_of_directed hdir).mp
    (elementaryGroup_le_iSup_map A hcov hu)

end KOneDescent
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.KOneDescent.subtype_mapMatrix_injective
#audit_axioms GroupApproximation.KOneDescent.exists_stage_units
#audit_axioms GroupApproximation.KOneDescent.elementaryGroup_le_iSup_map
#audit_axioms GroupApproximation.KOneDescent.elementaryImageStage_mono
#audit_axioms GroupApproximation.KOneDescent.exists_stage_elementary
