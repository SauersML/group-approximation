import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10WalkPetals.Side
import GroupApproximation.Meta.AxiomGuard

/-!
# A one-sided block off both arcs is a good lobe (step 2, first case)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

Step 2 of the local selection (`P10LocalSelect.p10LS_SelectionStatement`) chooses a lobe `B` of
the boundary cycle `c`.  This module handles the easiest choice.  Take a linear block
`c = X ++ B ++ Z` that is a simple closed walk, misses both arcs and some other dart of `c`, and
whose complementary excursion `Z ++ X` avoids `B` in its interior.  Then `B` is good.

* By `P10WalkPetals.infraPetal_oneSided_of_block` the rest of `c` is on one side of `B`.
* If it is on the side, a dart of each arc is off `B`, with its reverse off `c`.  So its reverse
  face (`s` for `a⁻¹`, `o` for `b`) is on the side too (`p10QM_side_alpha_iff`), which is case 1
  of `p10LS_Good`.
* If it is off the side, `B` is a closed cyclic block with the rest off its side and both arcs
  off it, which is case 2.

`p10LS_good_of_oneSidedBlock` is PROVED.  What step 2 still needs is the choice of such a block,
or of one of the other good lobes, under the rose premises.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

/-- **A one-sided simple block off both arcs is a good lobe** (Osin 9.7(b), `thm:hull`
infrastructure).  The arcs are `A = a⁻¹` and `T = b` of a split `c = s₁ ++ A ++ s₂ ++ T`. -/
theorem p10LS_good_of_oneSidedBlock {M : CombMap.{v}} {F : Finset M.Face} (c : BoundaryCycle M F)
    {o s k : M.Face} {bs : FaceBoundary M s} {bo : FaceBoundary M o} (a : CyclicArc bs.darts)
    (b : CyclicArc (bo.darts.reverse.map M.alpha)) {s₁ s₂ X B Z : List M.Dart}
    (hc : IsClosedDartWalk M c.cycle)
    (hsplit : c.cycle = s₁ ++ a.darts.reverse.map M.alpha ++ s₂ ++ b.darts)
    (hXBZ : c.cycle = X ++ B ++ Z) (hB : IsSimpleClosedWalk M B)
    (hint : ∀ e ∈ (Z ++ X).tail, ¬p10QS_OnB M B (M.vertexOf e))
    (hP : ∃ d ∈ c.cycle, d ∉ B)
    (hA : ∀ d ∈ a.darts.reverse.map M.alpha, d ∉ B) (hT : ∀ d ∈ b.darts, d ∉ B)
    (hAne : a.darts.reverse.map M.alpha ≠ []) (hTne : b.darts ≠ []) :
    p10LS_Good M F c o s k (a.darts.reverse.map M.alpha) b.darts B := by
  have hBc : ∀ d ∈ B, d ∈ c.cycle := fun d hd => by
    rw [hXBZ]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  obtain ⟨harc, hbrc⟩ := p10QM_arc_facts M c a b hsplit
  -- The reverse face of an arc dart off `B` is on the side of `B` iff the dart's face is.
  have hrev : ∀ d ∈ c.cycle, d ∉ B →
      (M.faceOf d ∈ sideFaces M B ↔ M.faceOf (M.alpha d) ∈ sideFaces M B) := by
    intro d hd hdB
    exact p10QM_side_alpha_iff M B hdB fun h => p10QM_alpha_not_mem M c hd (hBc _ h)
  have hblk : p10QM_CyclicBlock c.cycle B := Or.inl ⟨X, Z, hXBZ⟩
  rcases infraPetal_oneSided_of_block c hc hXBZ hint with hin | hout
  · -- The rest is on the side: case 1, with `o` and `s` on the side.
    obtain ⟨da, hda⟩ := List.exists_mem_of_ne_nil _ hAne
    obtain ⟨dt, hdt⟩ := List.exists_mem_of_ne_nil _ hTne
    obtain ⟨hdac, hdas⟩ := harc da hda
    obtain ⟨hdtc, hdto⟩ := hbrc dt hdt
    have hs : s ∈ sideFaces M B := by
      rw [← hdas]
      exact (hrev da hdac (hA da hda)).mp (hin da hdac (hA da hda))
    have ho : o ∈ sideFaces M B := by
      rw [← hdto]
      exact (hrev dt hdtc (hT dt hdt)).mp (hin dt hdtc (hT dt hdt))
    exact Or.inl ⟨hblk, hB, hP, hin, Or.inl ⟨ho, hs⟩⟩
  · -- The rest is off the side: case 2.
    exact Or.inr (Or.inl ⟨hblk, hB.isClosedDartWalk, hP, hout, hA, hT⟩)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_good_of_oneSidedBlock
