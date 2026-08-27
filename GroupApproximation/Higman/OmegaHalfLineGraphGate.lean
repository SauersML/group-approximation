import GroupApproximation.Higman.OmegaHalfLineRightInsertion
import GroupApproximation.Higman.TransportStar
import GroupApproximation.Higman.CentralHNNFreeLabelKernel

/-!
# The paired graph gate for one-sided Omega insertion

The proper edge cannot be a direct product of the insertion coordinate and a
half-row marker: the elements `(x,1)` would make the marker invisible.  The
correct object is their graph.  A basis letter indexed by a row conjugator
`h` is sent to the pair `(a^h,h)`, with the first coordinate embedded in the
slim stage-two group.  Restricting its basis to canonical right-tail codes
therefore records both facts simultaneously.

This file proves the exact one-letter gate and the productive arithmetic
step.  In particular, inserting a selected block into a gated pair remains a
genuine graph pair and is indexed by `beta + l` in canonical order.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Sequences supported in the right tail beginning at `m`. -/
def rightTailSeq (m : ℕ) : Set E :=
  {l : E | ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i}

/-- The conjugator-graph map with its first coordinate embedded into the slim
stage-two group. -/
noncomputable def slimGraphHom (m : ℕ) :
    FreeGroup ↥Conj.K →* SlimPi m × F₃ :=
  ((slimPiF3Hom m).comp Conj.cbHom).prod Star.evalHom

@[simp] theorem slimGraphHom_apply (m : ℕ) (w : FreeGroup ↥Conj.K) :
    slimGraphHom m w =
      (slimPiF3Hom m (Conj.cbHom w), Star.evalHom w) := rfl

theorem slimGraphHom_injective (m : ℕ) : Function.Injective (slimGraphHom m) := by
  intro u v huv
  apply Conj.cbHom_injective
  apply slimPiF3Hom_injective m
  exact congrArg Prod.fst huv

/-- The paired letter belonging to a sequence `l`. -/
noncomputable def slimGraphPair (m : ℕ) (l : E) : SlimPi m × F₃ :=
  (slimPiF3Hom m (aElt l), bElt l)

theorem slimGraphHom_of_bK (m : ℕ) (l : E) :
    slimGraphHom m (FreeGroup.of (bK l)) = slimGraphPair m l := by
  rw [slimGraphHom_apply, Conj.cbHom_of, Star.evalHom_of]
  rfl

/-- The graph subgroup whose literal basis indices are canonical right-tail
sequence codes. -/
noncomputable def slimRightGraph (m : ℕ) : Subgroup (SlimPi m × F₃) :=
  (Star.coordSub (bK '' rightTailSeq m)).map (slimGraphHom m)

/-- Exact basis test for the restricted paired graph. -/
theorem slimGraphHom_of_mem_slimRightGraph_iff
    (m : ℕ) (q : ↥Conj.K) :
    slimGraphHom m (FreeGroup.of q) ∈ slimRightGraph m ↔
      q ∈ bK '' rightTailSeq m := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have hword : w = FreeGroup.of q := slimGraphHom_injective m heq
    subst w
    exact CentralHNNFreeLabel.Coordinate.index_mem_of_of_mem_closure hw
  · intro hq
    refine ⟨FreeGroup.of q, ?_, rfl⟩
    exact Subgroup.subset_closure ⟨q, hq, rfl⟩

/-- **The right-tail marker is exact on sequence-labelled graph letters.** -/
theorem slimGraphPair_mem_slimRightGraph_iff (m : ℕ) (l : E) :
    slimGraphPair m l ∈ slimRightGraph m ↔ l ∈ rightTailSeq m := by
  rw [← slimGraphHom_of_bK,
    slimGraphHom_of_mem_slimRightGraph_iff]
  constructor
  · rintro ⟨f, hf, hfl⟩
    have hfl' : f = l := bK_injective hfl
    rwa [hfl'] at hf
  · intro hl
    exact ⟨l, hl, rfl⟩

/-- Insert a selected block in both correlated coordinates. -/
noncomputable def insertGraphPair (m : ℕ) (beta : E)
    (p : SlimPi m × F₃) : SlimPi m × F₃ :=
  ((slimPiOf m (slimGenCode m beta))⁻¹ * p.1 *
      slimPiOf m (slimGenCode m beta),
    bElt beta * p.2)

/-- **Productive graph-edge arithmetic.**  On the proper right-tail target,
paired insertion is exactly the canonical graph letter indexed by
`beta + l`. -/
theorem insertGraphPair_slimGraphPair_of_rightTail
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : l ∈ rightTailSeq m) :
    insertGraphPair m beta (slimGraphPair m l) =
      slimGraphPair m (beta + l) := by
  apply Prod.ext
  · exact slimGen_conj_aElt_eq_add_of_rightTail hbeta hl
  · exact (bElt_add_block_rightTail hbeta hl).symm

/-- The graph gate itself supplies the support hypothesis consumed by the
productive insertion theorem. -/
theorem insertGraphPair_slimGraphPair_of_mem_gate
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : slimGraphPair m l ∈ slimRightGraph m) :
    insertGraphPair m beta (slimGraphPair m l) =
      slimGraphPair m (beta + l) :=
  insertGraphPair_slimGraphPair_of_rightTail hbeta
    ((slimGraphPair_mem_slimRightGraph_iff m l).mp hl)

end Omega
end Higman
end GroupApproximation
