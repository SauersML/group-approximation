import GroupApproximation.Analysis.VoiculescuBlockRep

/-!
# (V4) Block-diagonal representations, and the absorption statement over them

This is the datum the assembly runs on: a representation together with a
decomposition of its space into finite-dimensional invariant blocks whose closed
span is everything.  On such a datum the intertwining step applies block by
block, the block isometries sum, and the defect is compact — that is the next
module.  Here are the datum, the statement, and the checks that neither is empty.

## What this Prop does and does not claim

`BlockDiagonalAbsorptionStatement` is a **special case** of
`AbsorptionContainmentStatement`, not a reformulation of it.  Not every
representation of a separable C⋆-algebra on a separable space decomposes into
finite-dimensional invariant blocks, and closing that gap is precisely where
Voiculescu's argument spends the quasicentral approximate unit.  The name says
`BlockDiagonal` for that reason: the reader should not be able to mistake it for
the general absorption theorem.

The statement is phrased over a closed `⋆`-subalgebra `A ⊆ B(H)` rather than over
an abstract `C` with an essential representation `σ`, because that is the shape
the intertwining step produces.  Converting between the two needs the image of a
`⋆`-homomorphism of C⋆-algebras to be closed, which is a theorem the tree does
not have; recorded here so nobody assumes the conversion is free.

## The model tests

`InvariantBlocks` is inhabited — `invariantBlocksOfFiniteDimensional` builds one
for any representation on a finite-dimensional space, with the whole space as the
single nonzero block — so the statement is not vacuous for want of data.  And
`isometry_of_blockDiagonal` reads off that the conclusion embeds `K`
isometrically into `H`, which is the constraint that keeps the statement from
asserting something about spaces that cannot receive one.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

-- As in `Analysis/VoiculescuBlockRep`, the algebra carries only what
-- `StarAlgHom` needs: in the application it is `↥A` for a star subalgebra of
-- `B(H)`, which is not a registered `CStarAlgebra`.
variable {C K : Type} [Semiring C] [Algebra ℂ C] [Star C] [NormedAddCommGroup K]
  [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## The datum -/

/-- **A decomposition of a representation into finite-dimensional invariant
blocks.** -/
structure InvariantBlocks (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K)) where
  /-- The blocks. -/
  sub : ℕ → Submodule ℂ K
  /-- Each block is finite-dimensional. -/
  finiteDimensional : ∀ m, FiniteDimensional ℂ ↥(sub m)
  /-- The blocks are pairwise orthogonal. -/
  orthogonal : OrthogonalFamily ℂ (fun m ↦ ↥(sub m)) fun m ↦ (sub m).subtypeₗᵢ
  /-- Their closed span is everything. -/
  total : ⊤ ≤ (⨆ m, sub m).topologicalClosure
  /-- Each block is invariant, hence — the algebra being `⋆`-closed — reducing. -/
  invariant : ∀ (m : ℕ) (a : C) (x : K), x ∈ sub m → rho a x ∈ sub m

namespace InvariantBlocks

variable {rho : C →⋆ₐ[ℂ] (K →L[ℂ] K)} (B : InvariantBlocks rho)

instance completeSpace (m : ℕ) : CompleteSpace ↥(B.sub m) := by
  haveI := B.finiteDimensional m
  exact FiniteDimensional.complete ℂ _

/-- The blocks make the source a Hilbert sum. -/
theorem isHilbertSum :
    IsHilbertSum ℂ (fun m ↦ ↥(B.sub m)) fun m ↦ (B.sub m).subtypeₗᵢ :=
  IsHilbertSum.mkInternal (F := B.sub) B.orthogonal B.total

/-- The representation carried by one block. -/
def rep (m : ℕ) : C →⋆ₐ[ℂ] (↥(B.sub m) →L[ℂ] ↥(B.sub m)) :=
  blockRep (B.sub m) rho (B.invariant m)

@[simp] theorem coe_rep_apply (m : ℕ) (a : C) (x : ↥(B.sub m)) :
    ((B.rep m a x : ↥(B.sub m)) : K) = rho a (x : K) := rfl

end InvariantBlocks

/-! ## The statement -/

/-- **(V4) over block-diagonal representations.**  A representation that
decomposes into finite-dimensional invariant blocks is contained, modulo the
compacts, in any essential subalgebra of `B(H)`. -/
def BlockDiagonalAbsorptionStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] (rho : ↥A →⋆ₐ[ℂ] (K →L[ℂ] K)),
        InvariantBlocks rho →
          ∃ W : K →L[ℂ] H, ContinuousLinearMap.adjoint W ∘L W = 1 ∧
            ∀ a : ↥A, IsCompactOperator ((a : H →L[ℂ] H) ∘L W - W ∘L rho a)

/-! ## The model tests -/

/-- **The datum is inhabited.**  Any representation on a finite-dimensional space
is block-diagonal, with the whole space as its single nonzero block, so the
statement above is not vacuous for want of data. -/
def invariantBlocksOfFiniteDimensional [FiniteDimensional ℂ K]
    (rho : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : InvariantBlocks rho where
  sub m := if m = 0 then ⊤ else ⊥
  finiteDimensional _ := inferInstance
  orthogonal := by
    have hbot : ∀ (p : Submodule ℂ K) (y : K), y ∈ p → p = ⊥ → y = 0 := by
      intro p y hy hp
      rw [hp] at hy
      exact (Submodule.mem_bot ℂ).mp hy
    intro i j hij v w
    have hzero : ((v : K) = 0) ∨ ((w : K) = 0) := by
      by_cases hi : i = 0
      · refine Or.inr (hbot _ (w : K) w.2 (if_neg fun h ↦ hij (hi.trans h.symm)))
      · exact Or.inl (hbot _ (v : K) v.2 (if_neg hi))
    rcases hzero with h | h
    · show ⟪(v : K), (w : K)⟫_ℂ = 0
      rw [h, inner_zero_left]
    · show ⟪(v : K), (w : K)⟫_ℂ = 0
      rw [h, inner_zero_right]
  total := by
    have hsup : (⨆ m : ℕ, (if m = 0 then (⊤ : Submodule ℂ K) else ⊥)) = ⊤ :=
      le_antisymm le_top (le_iSup_of_le 0 (by simp))
    rw [hsup]
    exact Submodule.le_topologicalClosure ⊤
  invariant m a x hx := by
    by_cases h : m = 0
    · rw [h, if_pos rfl]
      exact Submodule.mem_top
    · rw [if_neg h] at hx ⊢
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _

/-- **The conclusion embeds the source isometrically.**  As in the containment
form, this is what keeps the statement from asserting something about a source
too large to fit in `H`. -/
theorem isometry_of_blockDiagonal (h : BlockDiagonalAbsorptionStatement)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0)
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : ↥A →⋆ₐ[ℂ] (K →L[ℂ] K)) (B : InvariantBlocks rho) :
    ∃ W : K →L[ℂ] H, Isometry W := by
  obtain ⟨W, hWiso, -⟩ := h H A hAclosed hAK K rho B
  exact ⟨W, (ContinuousLinearMap.isometry_iff_adjoint_comp_self W).mpr hWiso⟩

end

end ShulmanFill
end GroupApproximation
