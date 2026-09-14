import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonSpanOfCopyClean
import GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler equalities of the decomposition walk of a two-gon

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonDecompositionEulerInput` (`Estimating/OsinAppendixEulerTwoGonSpanOfCopyClean`) asks that both
reclosings of a noncrossing decomposition walk `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` keep the Euler characteristic, when its source span is the source arc of `a`, a gap arc
and the source arc of `b`, and its target span runs from the start of the target arc of `a` to the end
of that of `b`.  Those arcs and the sides of `b` and `a` are the fields of a pocket walk from the cell
`i` in the positions of the section `j`, and the decomposition walk is that pocket walk with its two
halves swapped.  Every joint of the pocket walk is a boundary step of `a` or of `b`, whose sector is
free at least area, or a face step read backwards, whose stretch back is empty
(`PocketWalk.walk_isChain_closes_of_rel`).  Swapping the halves keeps the joints and the walk darts, so
every passage of the decomposition walk has a free sector, and
`IsNoncrossingClosedWalk.eulers_of_passageSectorFree` gives both equalities.  The edge conditions are
not used.

* `twoGonDecompositionEulerInput : TwoGonDecompositionEulerInput D lambda c eps W`.
* `osinTwoGonDecompositionEulerSection : OsinTwoGonDecompositionEulerSectionStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides SectorNoninterleaving Surgery.MapCollapse

private theorem passageSectorFree_append_comm {M : CombMap.{v}} {l₁ l₂ : List M.Dart}
    {d e : M.Dart} (h : PassageSectorFree M (l₁ ++ l₂) d e) : PassageSectorFree M (l₂ ++ l₁) d e := by
  have hmem : ∀ z, z ∈ l₁ ++ l₂ ↔ z ∈ l₂ ++ l₁ := fun z => List.perm_append_comm.mem_iff
  have hkeep : ∀ z, walkKeep M (l₁ ++ l₂) z ↔ walkKeep M (l₂ ++ l₁) z := fun z =>
    or_congr (hmem z) (hmem (M.alpha z))
  rcases h with ⟨m, hm, hfree⟩ | ⟨m, hm, hfree⟩
  · exact Or.inl ⟨m, hm, fun k hk0 hkm hk => hfree k hk0 hkm ((hkeep _).mpr hk)⟩
  · exact Or.inr ⟨m, hm, fun k hk0 hkm hk => hfree k hk0 hkm ((hkeep _).mpr hk)⟩

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The Euler equalities of the decomposition walk of a two-gon.** -/
theorem twoGonDecompositionEulerInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) :
    TwoGonDecompositionEulerInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts S hlea i j a b ha hb hab hja hjb horder _hclean source target hw hgap hstart hend
  obtain ⟨haS, -, hat⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily ha
  obtain ⟨hbS, -, hbt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hb
  obtain ⟨has, hatgt⟩ := S.nondegenerate a haS
  obtain ⟨hbs, hbtgt⟩ := S.nondegenerate b hbS
  obtain ⟨-, halo, -⟩ := hja
  obtain ⟨-, -, hbhi⟩ := hjb
  obtain ⟨gap, hsrc⟩ := hgap
  have hsl : 0 < source.length := by
    have h := congrArg List.length hsrc
    simp only [List.length_append, source.darts_length, a.2.sourceArc.darts_length] at h
    omega
  have hbend : b.2.targetArc.start.1 + b.2.targetArc.length ≤ (outerDarts S.diagram).length :=
    Nat.le_trans hbhi (PocketWalk.cut_le_length_outerDarts S.toRealizedSectionFamily j.succ)
  let K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ) :=
    { source := i
      sourceArc := source
      targetArc := target
      firstSide := b.2.leftSide
      secondSide := a.2.rightSide
      sourceArc_pos := hsl
      targetArc_pos := by omega
      firstSide_length_le := b.2.leftSide_length_le
      secondSide_length_le := a.2.rightSide_length_le
      firstSide_norm_le := b.2.leftSide_norm_le
      secondSide_norm_le := a.2.rightSide_norm_le
      lo_le := by omega
      le_hi := by omega }
  have hint := K.internal_not_walkKeep (x := a) (y := b) hlea rfl rfl (S.pairwise a haS b hbS hab)
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes_of_rel a b
    (R := fun d e => S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
      S.diagram.toCombMap.vertexOf e ∧ PassageSectorFree S.diagram.toCombMap K.walk d e)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.1)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_boundaryStep h,
      Or.inl (sectorFree_of_boundaryStep h hint.2)⟩)
    (fun _ _ h => ⟨vertexOf_alpha_eq_of_sigma h, Or.inr (sectorFree_of_sigma_eq h)⟩)
    hat hbt has hbs hatgt hbtgt rfl rfl gap.darts hsrc hstart hend hbend
  have hwalk : K.walk =
      b.2.leftSide ++ (invDarts S.diagram source.darts ++ a.2.rightSide ++ target.darts) := by
    show b.2.leftSide ++ invDarts S.diagram source.darts ++ a.2.rightSide ++ target.darts = _
    simp only [List.append_assoc]
  rw [hwalk] at hchain hcloses
  have hcc := ClosedWalkFaceColouring.closedChain_append_comm (P := b.2.leftSide)
    (Q := invDarts S.diagram source.darts ++ a.2.rightSide ++ target.darts) ⟨hchain, hcloses⟩
  obtain ⟨hchain', hcloses'⟩ := (ClosedWalkFaceColouring.closedChain_iff hw.ne_nil).mp hcc
  exact hw.eulers_of_passageSectorFree S.diagram.planar fun k =>
    passageSectorFree_append_comm (get_finRotate_of_isChain_closes hw.ne_nil hchain' hcloses' k).2

/-- **The Euler equalities of decomposition walks, uniformly in the parameters.** -/
theorem osinTwoGonDecompositionEulerSection :
    OsinTwoGonDecompositionEulerSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun rho _ W _ =>
    twoGonDecompositionEulerInput D lambda c eps W⟩⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.twoGonDecompositionEulerInput
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinTwoGonDecompositionEulerSection
