import GroupApproximation.Analysis.VoiculescuBlockRep

/-!
# (V4) Block-diagonal representations: the datum

This is the datum the assembly runs on: a representation together with a
decomposition of its space into finite-dimensional invariant blocks whose closed
span is everything.  On such a datum the intertwining step applies block by
block, the block isometries sum, and the defect is compact — that is
`Analysis/VoiculescuBlockAbsorption`.  Here are the datum and the check that it
is not empty.

## Why there is no absorption statement in this file

There was one, and it was **retired**, because it asked for its conclusion under
hypotheses that cannot supply it.  The construction needs `↥A` separable — the
recursion names only countably many elements of `A` while the conclusion is
claimed for every `a`, and the passage between them is density, which
Voiculescu's theorem genuinely requires — and it needs `ρ` contractive, which is
automatic for a `⋆`-homomorphism of C⋆-algebras but unavailable here because `↥A`
carries no registered `CStarAlgebra` instance.  What is actually proved is
`SeparableBlockDiagonalAbsorptionStatement`, in
`Analysis/VoiculescuBlockAbsorption`, which is named for the difference.  It is
not recorded here as a refuted `Prop` because nothing established that the weaker
form is false, only that it does not follow; a `Prop` in that position would be a
statement nobody can either use or refute.

Either way it is a **special case** of `AbsorptionContainmentStatement` and not a
reformulation of it: not every representation of a separable C⋆-algebra on a
separable space decomposes into finite-dimensional invariant blocks, and closing
that gap is precisely where Voiculescu's argument spends the quasicentral
approximate unit.

## The model test

`InvariantBlocks` is inhabited — `invariantBlocksOfFiniteDimensional` builds one
for any representation on a finite-dimensional space, with the whole space as its
single nonzero block — so nothing built on the datum is vacuous for want of it.
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

/-! ## The model test -/

/-- **The datum is inhabited.**  Any representation on a finite-dimensional space
is block-diagonal, with the whole space as its single nonzero block, so the
datum is inhabited and nothing built on it is vacuous for want of data. -/
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

end

end ShulmanFill
end GroupApproximation
