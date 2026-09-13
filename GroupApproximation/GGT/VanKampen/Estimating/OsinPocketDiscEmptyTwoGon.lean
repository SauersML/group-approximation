import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscMerge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerEmptyTwoGon
import GroupApproximation.Meta.AxiomGuard

/-!
# The empty two-gon of `Φ'_M`

`EmptyTwoGonInput` (`Estimating/OsinAppendixEulerEmptyTwoGon.lean`) is the step of the proof of
Osin's Lemma 9.7(a) (arXiv:math/0411039v3) that puts a vertex of `Φ_M` inside every 2-gon of
`Φ'_M`: "otherwise one can include the ε-contiguity subdiagrams corresponding to the edges `e`
and `f` of `Φ'_M` into a single ε-contiguity subdiagram in the obvious way, contrary to the
definition of `M`."  This file proves it (`emptyTwoGonInput_holds`).

The proof collapses the pocket `P` through its disc region
(`Surgery.InnerDiscRegion.ofPocketRegion`).  The pocket may be pinched, so there is no embedded
boundary to use.  The decomposition hypothesis on the reversed outer cycle of `P` is a rotation of
the cycle of the disc region, so the merged face is one contiguity region of the cell `i` to the
section `j` (`Surgery.InnerDiscRegion.mergedGeometry`), whose arcs are at least as long as those
of `a` and `b` together.  Every other selected region avoids `P` and is carried through the
collapse, so `false_of_disc_collapse_singleton` contradicts the choice of `M`.  The least-area
hypothesis and the containment of the faces of `a` and `b` in `P` are not used.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}

/-- **`EmptyTwoGonInput` holds**: an empty two-gon of `Φ'_M` contradicts the choice of the
distinguished system. -/
theorem emptyTwoGonInput_holds (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : EmptyTwoGonInput.{u, w, v} D lambda c eps W := by
  classical
  unfold EmptyTwoGonInput
  intro _ cuts _ S i j a ha b hb hab hja hjb P _ _ hcells hothers source target hsource hstart
    hend htarget hdecomp
  obtain ⟨_, hja1, _⟩ := hja
  obtain ⟨_, _, hjb2⟩ := hjb
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  let R := Surgery.InnerDiscRegion.ofPocketRegion P hcells
  have hrot : R.region.cycle.rotate k =
      source.reverseDarts ++ a.2.rightSide ++ targetBoundaryDarts S.diagram none target ++
        b.2.leftSide :=
    hk.symm.trans hdecomp
  have hright := a.2.rightSide_length_le
  have hleft := b.2.leftSide_length_le
  have hrightNorm := a.2.rightSide_norm_le
  have hleftNorm := b.2.leftSide_norm_le
  let H := R.mergedGeometry source target hrot hright hleft hrightNorm hleftNorm
  have hHsource : H.sourceArc.length = source.length :=
    R.mergedGeometry_sourceArc_length source target hrot hright hleft hrightNorm hleftNorm
  have hHtarget : H.targetArc.length = target.length :=
    R.mergedGeometry_targetArc_length source target hrot hright hleft hrightNorm hleftNorm
  have hHstart : H.targetArc.start.1 = target.start.1 :=
    R.mergedGeometry_targetArc_start source target hrot hright hleft hrightNorm hleftNorm
  have hmem : ∀ x ∈ RegionCandidate.exteriorAt S.family i, x ∈ S.family := fun _ hx =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hsub : ({a, b} : Finset (RegionCandidate D eps S.diagram)) ⊆ S.family :=
    Finset.insert_subset_iff.mpr ⟨hmem a ha, Finset.singleton_subset_iff.mpr (hmem b hb)⟩
  have hcard : 2 ≤ ({a, b} : Finset (RegionCandidate D eps S.diagram)).card :=
    (Finset.card_pair_eq_two_iff.mpr hab).ge
  have havoid : ∀ x ∈ S.family, x ∉ ({a, b} : Finset (RegionCandidate D eps S.diagram)) →
      Disjoint x.1 R.faces := fun x hx hxab =>
    hothers x hx (fun h => hxab (by simp [h])) (fun h => hxab (by simp [h]))
  have hrespects : RegionCandidate.RespectsSections cuts
      (⟨{R.merged}, H⟩ : RegionCandidate D eps R.diagram) := by
    refine fun _ => ⟨j, rfl, ?_, ?_⟩
    · show cuts.cut j.castSucc ≤ H.targetArc.start.1
      omega
    · show H.targetArc.start.1 + H.targetArc.length ≤ cuts.cut j.succ
      omega
  obtain ⟨has, hat⟩ := S.nondegenerate a (hmem a ha)
  have hHs : 0 < H.sourceArc.length := by omega
  have hHt : 0 < H.targetArc.length := by omega
  have hweight : EstimatingSelection.familyWeight RegionCandidate.weight
      ({a, b} : Finset (RegionCandidate D eps S.diagram)) ≤
        H.sourceArc.length + H.targetArc.length := by
    unfold EstimatingSelection.familyWeight
    rw [Finset.sum_pair hab, hHsource, hHtarget]
    simp only [RegionCandidate.weight]
    omega
  exact S.false_of_disc_collapse_singleton R {a, b} hsub hcard havoid H hrespects hHs hHt
    hweight

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.emptyTwoGonInput_holds
