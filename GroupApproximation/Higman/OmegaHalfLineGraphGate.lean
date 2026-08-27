import GroupApproximation.Higman.OmegaHalfLineRightInsertion
import GroupApproximation.Higman.TransportStar
import GroupApproximation.Higman.CentralHNNFreeLabelKernel
import GroupApproximation.Higman.ExplicitFreeEdge
import GroupApproximation.Higman.OmegaHalfLineAscendingCriterion

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

/-! ## The literal proper free edge -/

/-- A right-tail sequence regarded as a graph-basis label. -/
abbrev RightTailIndex (m : ℕ) := ↥(rightTailSeq m)

/-- The source index map into the conjugator basis. -/
noncomputable def rightTailIndexToK (m : ℕ) : RightTailIndex m → ↥Conj.K :=
  fun l => bK (l : E)

theorem rightTailIndexToK_injective (m : ℕ) :
    Function.Injective (rightTailIndexToK m) := by
  intro l r hlr
  exact Subtype.ext (bK_injective hlr)

/-- The target index map obtained by prepending the selected window block. -/
noncomputable def insertedRightTailIndexToK
    (m : ℕ) (beta : E) : RightTailIndex m → ↥Conj.K :=
  fun l => bK (beta + (l : E))

theorem insertedRightTailIndexToK_injective (m : ℕ) (beta : E) :
    Function.Injective (insertedRightTailIndexToK m beta) := by
  intro l r hlr
  apply Subtype.ext
  have hadd : beta + (l : E) = beta + (r : E) := bK_injective hlr
  exact add_left_cancel hadd

/-- Evaluate a free word in right-tail graph letters. -/
noncomputable def rightGraphSource (m : ℕ) :
    FreeGroup (RightTailIndex m) →* SlimPi m × F₃ :=
  (slimGraphHom m).comp (FreeGroup.map (rightTailIndexToK m))

/-- Evaluate the same free word after prepending `beta` to every graph
letter. -/
noncomputable def rightGraphTarget (m : ℕ) (beta : E) :
    FreeGroup (RightTailIndex m) →* SlimPi m × F₃ :=
  (slimGraphHom m).comp (FreeGroup.map (insertedRightTailIndexToK m beta))

theorem rightGraphSource_injective (m : ℕ) :
    Function.Injective (rightGraphSource m) :=
  (slimGraphHom_injective m).comp
    (FreeGroup.map_injective (rightTailIndexToK_injective m))

theorem rightGraphTarget_injective (m : ℕ) (beta : E) :
    Function.Injective (rightGraphTarget m beta) :=
  (slimGraphHom_injective m).comp
    (FreeGroup.map_injective (insertedRightTailIndexToK_injective m beta))

@[simp] theorem rightGraphSource_of (m : ℕ) (l : RightTailIndex m) :
    rightGraphSource m (FreeGroup.of l) = slimGraphPair m (l : E) := by
  change slimGraphHom m (FreeGroup.of (bK (l : E))) = slimGraphPair m (l : E)
  rw [slimGraphHom_of_bK]

@[simp] theorem rightGraphTarget_of (m : ℕ) (beta : E)
    (l : RightTailIndex m) :
    rightGraphTarget m beta (FreeGroup.of l) =
      slimGraphPair m (beta + (l : E)) := by
  change slimGraphHom m (FreeGroup.of (bK (beta + (l : E)))) =
    slimGraphPair m (beta + (l : E))
  rw [slimGraphHom_of_bK]

/-- **The honest proper free-edge datum for one selected block.**  Its source
basis consists of right-tail graph pairs and its target basis consists of the
same pairs after canonical block insertion. -/
noncomputable def rightInsertionEdge
    (m : ℕ) (beta : E) :
    ExplicitFreeEdge.Data (RightTailIndex m) (SlimPi m × F₃) where
  source := rightGraphSource m
  target := rightGraphTarget m beta
  source_injective := rightGraphSource_injective m
  target_injective := rightGraphTarget_injective m beta

/-- The HNN stable letter for the literal graph edge performs canonical
right insertion on every basis pair. -/
theorem rightInsertionEdge_stable_conj
    (m : ℕ) (beta : E) (l : RightTailIndex m) :
    (HNNExtension.t : ExplicitFreeEdge.Extension (rightInsertionEdge m beta)) *
        HNNExtension.of (slimGraphPair m (l : E)) * HNNExtension.t⁻¹ =
      HNNExtension.of (slimGraphPair m (beta + (l : E))) := by
  simpa only [rightInsertionEdge, rightGraphSource_of, rightGraphTarget_of]
    using ExplicitFreeEdge.stable_conj_source
      (rightInsertionEdge m beta) (FreeGroup.of l)

/-! ## The two edge images as literal restricted graphs -/

/-- The source range of the explicit edge is exactly the graph restricted to
right-tail sequence labels.  This is the bridge from the infinite free-basis
description to a finite cutter: a benign witness only has to cut out
`slimRightGraph`. -/
theorem rightInsertion_sourceSubgroup_eq_slimRightGraph
    (m : ℕ) (beta : E) :
    ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta) =
      slimRightGraph m := by
  apply le_antisymm
  · rintro x ⟨w, -, rfl⟩
    refine ⟨FreeGroup.map (rightTailIndexToK m) w, ?_, rfl⟩
    induction w using FreeGroup.induction_on with
    | C1 => exact Subgroup.one_mem _
    | of l =>
        exact Subgroup.subset_closure
          ⟨bK (l : E), ⟨(l : E), l.property, rfl⟩, rfl⟩
    | inv_of l hl =>
        rw [map_inv, FreeGroup.map.of]
        exact Subgroup.inv_mem _
          (Subgroup.subset_closure
            ⟨bK (l : E), ⟨(l : E), l.property, rfl⟩, rfl⟩)
    | mul u v hu hv =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hu hv
  · rintro x ⟨w, hw, rfl⟩
    have hrange : w ∈ (FreeGroup.map (rightTailIndexToK m)).range := by
      refine Subgroup.closure_induction (p := fun z _ =>
        z ∈ (FreeGroup.map (rightTailIndexToK m)).range) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨q, ⟨l, hl, rfl⟩, rfl⟩
        exact ⟨FreeGroup.of ⟨l, hl⟩, by simp [rightTailIndexToK]⟩
      · exact Subgroup.one_mem _
      · intro u v _ _ hu hv
        exact Subgroup.mul_mem _ hu hv
      · intro u _ hu
        exact Subgroup.inv_mem _ hu
    obtain ⟨v, hv⟩ := hrange
    refine ⟨v, Subgroup.mem_top v, ?_⟩
    change slimGraphHom m (FreeGroup.map (rightTailIndexToK m) v) =
      slimGraphHom m w
    rw [hv]

/-- The inserted target graph, still indexed by the same right-tail free
basis. -/
noncomputable def slimInsertedRightGraph (m : ℕ) (beta : E) :
    Subgroup (SlimPi m × F₃) :=
  (Star.coordSub (bK '' ((fun l : E => beta + l) '' rightTailSeq m))).map
    (slimGraphHom m)

/-- The target range of the explicit edge is the inserted restricted graph.
This gives the second exact comap/range equation required by a finite-rank
compression. -/
theorem rightInsertion_targetSubgroup_eq_slimInsertedRightGraph
    (m : ℕ) (beta : E) :
    ExplicitFreeEdge.targetSubgroup (rightInsertionEdge m beta) =
      slimInsertedRightGraph m beta := by
  apply le_antisymm
  · rintro x ⟨w, -, rfl⟩
    refine ⟨FreeGroup.map (insertedRightTailIndexToK m beta) w, ?_, rfl⟩
    induction w using FreeGroup.induction_on with
    | C1 => exact Subgroup.one_mem _
    | of l =>
        exact Subgroup.subset_closure
          ⟨bK (beta + (l : E)),
            ⟨beta + (l : E), ⟨(l : E), l.property, rfl⟩, rfl⟩, rfl⟩
    | inv_of l hl =>
        rw [map_inv, FreeGroup.map.of]
        exact Subgroup.inv_mem _
          (Subgroup.subset_closure
            ⟨bK (beta + (l : E)),
              ⟨beta + (l : E), ⟨(l : E), l.property, rfl⟩, rfl⟩, rfl⟩)
    | mul u v hu hv =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hu hv
  · rintro x ⟨w, hw, rfl⟩
    have hrange : w ∈ (FreeGroup.map
        (insertedRightTailIndexToK m beta)).range := by
      refine Subgroup.closure_induction (p := fun z _ =>
        z ∈ (FreeGroup.map (insertedRightTailIndexToK m beta)).range)
        ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨q, ⟨l, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩
        exact ⟨FreeGroup.of ⟨r, hr⟩,
          by simp [insertedRightTailIndexToK]⟩
      · exact Subgroup.one_mem _
      · intro u v _ _ hu hv
        exact Subgroup.mul_mem _ hu hv
      · intro u _ hu
        exact Subgroup.inv_mem _ hu
    obtain ⟨v, hv⟩ := hrange
    refine ⟨v, Subgroup.mem_top v, ?_⟩
    change slimGraphHom m
        (FreeGroup.map (insertedRightTailIndexToK m beta) v) =
      slimGraphHom m w
    rw [hv]

/-! ## Exact base return for the literal edge -/

/-- The two edge images are the complete base answer after adjoining the
stable letter to the source image. -/
noncomputable def rightInsertionHull (m : ℕ) (beta : E) :
    Subgroup (SlimPi m × F₃) :=
  ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta) ⊔
    ExplicitFreeEdge.targetSubgroup (rightInsertionEdge m beta)

/-- The literal right-insertion edge satisfies both asymmetric gate clauses.
The reverse clause is available only on the target image; this is the proper
edge restriction absent from the refuted automorphic tower. -/
theorem rightInsertion_oneSidedGate (m : ℕ) (beta : E) :
    OneSidedGate
      (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
      (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta))
      (rightInsertionHull m beta) := by
  refine ⟨le_sup_left, ?_, ?_⟩
  · intro a _
    exact Subgroup.mem_sup_right
      (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta) a).property
  · intro b _
    exact Subgroup.mem_sup_left
      ((ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta)).symm b).property

/-- The target image is already forced into the stable hull of the source:
apply the forward edge map to the corresponding source element. -/
theorem target_le_rightInsertion_stableHull (m : ℕ) (beta : E) :
    ExplicitFreeEdge.targetSubgroup (rightInsertionEdge m beta) ≤
      HNNDescent.stableHull
        (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
        (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta)) := by
  intro y hy
  let b : ExplicitFreeEdge.targetSubgroup (rightInsertionEdge m beta) := ⟨y, hy⟩
  let a := (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta)).symm b
  have ha : (a : SlimPi m × F₃) ∈
      HNNDescent.stableHull
        (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
        (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta)) :=
    HNNDescent.le_stableHull
      (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
      (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta)) a.property
  have hb := (HNNDescent.stable_stableHull
      (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
      (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta))).fwd a ha
  simpa [a, b] using hb

/-- **Full one-sided base cutter equality for one selected block.**  The
subgroup generated by the source graph and the HNN stable letter meets the
base in exactly the join of the source and inserted target graphs. -/
theorem rightInsertion_generatedBase_eq (m : ℕ) (beta : E) :
    HNNDescent.generatedBase
        (ExplicitFreeEdge.edgeEquiv (rightInsertionEdge m beta))
        (ExplicitFreeEdge.sourceSubgroup (rightInsertionEdge m beta)) =
      rightInsertionHull m beta := by
  rw [← HNNDescent.stableHull_eq_generatedBase]
  apply le_antisymm
  · exact HNNDescent.stableHull_le _ le_sup_left
      (rightInsertion_oneSidedGate m beta).stable
  · exact sup_le
      (HNNDescent.le_stableHull _ _)
      (target_le_rightInsertion_stableHull m beta)

end Omega
end Higman
end GroupApproximation
