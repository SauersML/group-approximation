import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSectorFreeVertexCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkNoninterleavingJoints
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler equalities of the pocket walks

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The kept relator cell of a pocket comes from the pocket region of its walk, built from the Euler
equalities of the two reclosings (`PocketRegion.ofNoncrossingClosedWalkEuler`).  The named residuals
of those equalities are `SectionPocketWalkEulerStatement` (`Estimating/OsinPocketKeptCellSection`)
and `CellPocketWalkEulerStatement` (`Estimating/OsinPocketCellSideRelatorCellEuler`).

Every joint of a pocket walk is a boundary step of one of the two regions, whose sector is free at
least area, or a face step read backwards, whose stretch back is empty
(`PocketWalk.walk_isChain_closes_of_rel`, `CellPocketWalk.walk_isChain_closes_of_rel`).  So every
passage has a free sector, and both reclosings keep the Euler characteristic
(`IsNoncrossingClosedWalk.eulers_of_passageSectorFree`).

* `sectionPocketWalkEuler : SectionPocketWalkEulerStatement`.
* `cellPocketWalkEuler : CellPocketWalkEulerStatement`.
* `sectionPocketKeptCell : SectionPocketKeptCellStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides SectorNoninterleaving Surgery.MapCollapse

private theorem getLast_head_of_mem_closes {α : Type*} {R : α → α → Prop} {l : List α}
    (hne : l ≠ []) (h : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b) : R (l.getLast hne) (l.head hne) :=
  h _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast hne)) _
    (Option.mem_def.mpr (List.head?_eq_some_head hne))

/-- **The Euler equalities of the section pocket walk.** -/
theorem sectionPocketWalkEuler : SectionPocketWalkEulerStatement.{u, w, v} := by
  intro G _ Lambda D lambda c eps W Delta cuts S hlea i j x y hx hy hxy hjx hjy K hsource hfirst
    hsecond hgap hstart hend hclean hw
  obtain ⟨hxS, -, hxt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hx
  obtain ⟨hyS, -, hyt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hy
  obtain ⟨hxs, hxtgt⟩ := S.nondegenerate x hxS
  obtain ⟨hys, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨-, -, hyhi⟩ := hjy
  have hyend : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts S.diagram).length :=
    Nat.le_trans hyhi (PocketWalk.cut_le_length_outerDarts S.toRealizedSectionFamily j.succ)
  obtain ⟨Gap, hsrc⟩ := hgap
  have hint := K.internal_not_walkKeep hlea hfirst hsecond (S.pairwise x hxS y hyS hxy)
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes_of_rel x y
    (R := fun d e => S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
      S.diagram.toCombMap.vertexOf e ∧ PassageSectorFree S.diagram.toCombMap K.walk d e)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.1)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.2)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_sigma h, Or.inr (sectorFree_of_sigma_eq h)⟩)
    hxt hyt hxs hys hxtgt hytgt hfirst hsecond Gap.darts hsrc hstart hend hyend
  exact hw.eulers_of_passageSectorFree S.diagram.planar fun k =>
    (get_finRotate_of_isChain_closes hw.ne_nil hchain
      (getLast_head_of_mem_closes hw.ne_nil hcloses) k).2

/-- **The Euler equalities of the cell pocket walk.** -/
theorem cellPocketWalkEuler : CellPocketWalkEulerStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts hlea S i j a b ha hb hab hij hai hbi hclean K hfirst
    hsecond h₁ h₂ hw
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  obtain ⟨G₁, hG₁⟩ := h₁
  obtain ⟨G₂, hG₂⟩ := h₂
  have hint := K.internal_not_walkKeep hlea' hfirst hsecond (S.pairwise a ha b hb hab)
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes_of_rel
    (R := fun d e => S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
      S.diagram.toCombMap.vertexOf e ∧ PassageSectorFree S.diagram.toCombMap K.walk d e)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.1)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.2)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_sigma h, Or.inr (sectorFree_of_sigma_eq h)⟩)
    hij hai hbi
    (RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) i)
    (RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb) i)
    (RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha) j)
    (RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb) j)
    hfirst hsecond G₁.darts G₂.darts hG₁ hG₂
  exact hw.eulers_of_passageSectorFree S.diagram.planar fun k =>
    (get_finRotate_of_isChain_closes hw.ne_nil hchain
      (getLast_head_of_mem_closes hw.ne_nil hcloses) k).2

/-- **The kept cell of the section pocket.** -/
theorem sectionPocketKeptCell : SectionPocketKeptCellStatement.{u, w, v} :=
  sectionPocketKeptCell_of_euler sectionPocketWalkEuler

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.sectionPocketWalkEuler
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketWalkEuler
#audit_closed_axioms GroupApproximation.GGT.VanKampen.sectionPocketKeptCell
