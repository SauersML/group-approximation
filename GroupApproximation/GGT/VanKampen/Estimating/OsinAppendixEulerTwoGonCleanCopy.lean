import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDoublingTransport
import GroupApproximation.GGT.VanKampen.SurgeryOuterThickeningInvariant
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickeningSix
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean copy of a two-gon from the thickenings

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonCleanCopyInput` (`Estimating/OsinAppendixEulerTwoGonCopyRoute`) asks for a clean two-gon on
another optimal family over the same diagram and cuts: all label pairs of the two-gon satisfy the edge
conditions `PocketWalk.CopyCleanAt`.  The closed thickenings reach a diagram free of every offending
dart, and a clean two-gon is carried through each doubling step by the named step Props of
`Estimating/OsinAppendixEulerTwoGonDoublingTransport`.

* `twoGonCopyCleanAt_of_free`: on a least-area family with no outer spur, no outer cell dart, no
  outer side dart, no cell-side dart, no cell hair and no region-pair dart, every pair of distinct
  exterior regions of one cell satisfies the edge conditions.  A cell with two such regions has a face
  of more than one dart, since otherwise both source arcs would be its one dart and the face across it
  would lie in both regions.
* `twoGonCleanCopyInput_of_steps`: `TwoGonCleanCopyInput` from the six step Props, over the outer
  spur, outer cell, outer side, cell side, cell hair and region-pair thickenings in that order.  The
  outer conditions ride along the inner steps through `CellSideThickening.outerClean_of_step`,
  `CellHairThickening.noOuterSideDart`, `CellHairThickening.noCellSideDart` and the region-pair step
  lemmas.
* `osinTwoGonCleanCopySection_of_steps`, `osinTwoGonHoldsSection_of_stepsEuler`: the section leaf,
  and C6′ uniformly in the parameters from the six step Props and the Euler equalities.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The edge conditions from the free diagram.** -/
theorem twoGonCopyCleanAt_of_free (hlea : Delta.LeastArea)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hspur : ∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x)
    (hocell : ∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x)
    (hoside : ∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x)
    (hcside : ∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x)
    (hhair : ∀ x, ¬ CellHairThickening.IsCellHair S.diagram x)
    (hpair : ∀ x, ¬ RegionPairThickening.IsRegionPairDart S.diagram S.family x)
    {i : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b) :
    PocketWalk.CopyCleanAt S.diagram i a b := by
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  obtain ⟨haK, hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbK, hbi⟩ := Finset.mem_filter.mp hb
  have haS : a ∈ S.family := (Finset.mem_filter.mp haK).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp hbK).1
  have hcellFace : ∀ r ∈ S.family, (cell S.diagram i).face ∉ r.1 :=
    fun r _ => (r.2.innerGRegion hleaS).cells_avoid _ (cell_mem S.diagram i)
  have hacross : ∀ (r : RegionCandidate D eps S.diagram) (p : S.diagram.toCombMap.Dart),
      p ∈ r.2.sourceArc.darts →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha p) ∈ r.1 := by
    intro r p hp
    have hmem : S.diagram.toCombMap.alpha p ∈ r.2.boundary.cycle := by
      rw [r.2.boundary_decomposition]
      simp only [List.mem_append]
      refine Or.inl (Or.inl (Or.inl ?_))
      simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
      exact ⟨p, hp, rfl⟩
    exact ((r.2.boundary.cycle_mem_iff _).mp hmem).1
  have hlenCell : 1 < (S.diagram.faceBoundary (cell S.diagram i).face).darts.length := by
    by_contra hle
    have hle' : (S.diagram.faceBoundary (cell S.diagram i).face).darts.length ≤ 1 := by omega
    have key : ∀ x ∈ (S.diagram.faceBoundary (cell S.diagram i).face).darts,
        ∀ y ∈ (S.diagram.faceBoundary (cell S.diagram i).face).darts, x = y := by
      intro x hx y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      obtain ⟨k', hk', rfl⟩ := List.mem_iff_getElem.mp hy
      have hk0 : k = 0 := by omega
      have hk0' : k' = 0 := by omega
      subst hk0 hk0'
      rfl
    obtain ⟨pa, hpa⟩ := a.2.sourceArc.exists_mem_darts (S.nondegenerate a haS).1
    obtain ⟨pb, hpb⟩ := b.2.sourceArc.exists_mem_darts (S.nondegenerate b hbS).1
    have hpa' : pa ∈ cellDarts S.diagram a.2.source := a.2.sourceArc.mem_cycle_of_mem_darts hpa
    have hpb' : pb ∈ cellDarts S.diagram b.2.source := b.2.sourceArc.mem_cycle_of_mem_darts hpb
    rw [hai] at hpa'
    rw [hbi] at hpb'
    have hpab : pa = pb := key pa hpa' pb hpb'
    have hfa := hacross a pa hpa
    have hfb := hacross b pb hpb
    rw [← hpab] at hfb
    exact hab (RegionCandidate.eq_of_face_mem_of_face_mem S.pairwise haS hbS hfa hfb)
  have hsideReg : ∀ d ∈ b.2.leftSide ++ a.2.rightSide, ∃ r ∈ S.family,
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha d) ∈ r.2.rightSide ++ r.2.leftSide := by
    intro d hd
    rw [S.diagram.toCombMap.alpha_involutive d]
    rcases List.mem_append.mp hd with h | h
    · exact ⟨b, hbS, List.mem_append_right _ h⟩
    · exact ⟨a, haS, List.mem_append_left _ h⟩
  exact
    { spur := fun d h1 h2 => hspur d ⟨h1, h2⟩
      cell_self := fun d h1 h2 =>
        hhair d ⟨h1.trans h2.symm, cell S.diagram i, cell_mem S.diagram i, h1.symm⟩
      cell_outer := fun d h1 h2 => hocell (S.diagram.toCombMap.alpha d)
        ⟨h2, cell S.diagram i, cell_mem S.diagram i,
          by rw [S.diagram.toCombMap.alpha_involutive d]; exact h1.symm⟩
      regions := RegionPairThickening.regions_of_noRegionPairDart hpair haS hbS hab
        (fun _ hdx hdy => RegionPairThickening.one_lt_length_or_of_regions hdx hdy)
      side_cell := fun d hd h => hcside (S.diagram.toCombMap.alpha d)
        ⟨⟨cell S.diagram i, cell_mem S.diagram i, h⟩, by rw [h]; exact hlenCell,
          fun r hr => by rw [h]; exact hcellFace r hr, hsideReg d hd⟩
      side_outer := fun d hd h => hoside (S.diagram.toCombMap.alpha d) ⟨h, hsideReg d hd⟩ }

/-- **A clean copy of a two-gon from the six step Props.** -/
theorem twoGonCleanCopyInput_of_steps
    (hspurStep : TwoGonSpurStepStatement.{u, w, v})
    (hocellStep : TwoGonOuterCellStepStatement.{u, w, v})
    (hosideStep : TwoGonOuterSideStepStatement.{u, w, v})
    (hcsideStep : TwoGonCellSideStepStatement.{u, w, v})
    (hhairStep : TwoGonCellHairStepStatement.{u, w, v})
    (hpairStep : TwoGonRegionPairStepStatement.{u, w, v}) :
    TwoGonCleanCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  have hS0 : HasCleanTwoGon S := ⟨hloops, hmulti, a₀, ha₀, hat, P, f, hf, hcorner, hcell⟩
  obtain ⟨y, -, -, -, -, j, hya, hyb, -, -, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  have hlen0 : 1 < Delta.boundaryWord.length := by
    have h1 := hjb.2.2
    have h2 := cuts.cut_le_length j.succ
    have hnda := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hya).1).1
    have hndb := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hyb).1).1
    omega
  have hvalueOf : ∀ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      ∀ C ∈ T.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
    fun T C hC => DiscDiagram.leastArea_listVal_word_ne_one (T.equiv.leastArea hlea) C hC
  obtain ⟨S₁, -, -, hspur₁, -, -, hP₁⟩ :=
    OuterSpurThickening.exists_spurFree_of_invariant HasCleanTwoGon
      (fun T k hlen hs hT => hspurStep hlea T k hlen hs hT) S hS0
  obtain ⟨S₂, -, -, hspur₂, hcell₂, -, -, -, hP₂⟩ :=
    OuterCellThickening.exists_cellFree_of_invariant HasCleanTwoGon
      (fun T k hlen hv hT => hocellStep hlea T k hlen hv hT) S₁ hlen0 (hvalueOf S₁) hspur₁ hP₁
  obtain ⟨S₃, -, -, hspur₃, hcell₃, hside₃, -, -, -, hP₃⟩ :=
    OuterSideThickening.exists_sideFree_of_invariant HasCleanTwoGon
      (fun T k hlen ht hT => hosideStep hlea T k hlen ht hT) S₂ hlen0 (hvalueOf S₂) hspur₂
      hcell₂ hP₂
  obtain ⟨S₄, -, -, hcside₄, -, -, hclean₄, hP₄⟩ :=
    CellSideThickening.exists_cellSideFree_of_invariant
      (fun T => CellSideThickening.OuterClean T ∧ HasCleanTwoGon T)
      (fun T g k hlen hg hv hT => ⟨CellSideThickening.outerClean_of_step T g k hlen hg hv hT.1,
        hcsideStep hlea T g k hlen hg hv hT.2⟩)
      S₃ ⟨⟨hvalueOf S₃, hspur₃, hcell₃, hside₃⟩, hP₃⟩
  obtain ⟨hvalue₄, hspur₄, hcell₄, hside₄⟩ := hclean₄
  obtain ⟨S₅, -, -, hspur₅, hcell₅, hhair₅, -, -, -, hside₅, hcside₅, hP₅⟩ :=
    CellHairThickening.exists_cellHairFree_of_invariant
      (fun T => (∀ x, ¬ OuterSideThickening.IsOuterSideDart T.diagram T.family x) ∧
        (∀ x, ¬ CellSideThickening.IsCellSideDart T.diagram T.family x) ∧ HasCleanTwoGon T)
      (fun T g k hlen hg hv hT =>
        ⟨CellHairThickening.noOuterSideDart T.diagram g k hlen hg T.family hv hT.1,
          CellHairThickening.noCellSideDart T.diagram g k hlen hg T.family hv (hvalueOf T) hT.2.1,
          hhairStep hlea T g k hlen hg hv hT.2.2⟩)
      S₄ hvalue₄ hspur₄ hcell₄ ⟨hside₄, hcside₄, hP₄⟩
  obtain ⟨S₆, -, -, hpair₆, -, -, -, hspur₆, hcell₆, hside₆, hcside₆, hhair₆, hP₆⟩ :=
    RegionPairThickening.exists_regionPairFree_of_invariant
      (fun T => (∀ x, ¬ OuterSpurThickening.IsOuterSpur T.diagram x) ∧
        (∀ x, ¬ OuterCellThickening.IsOuterCellDart T.diagram x) ∧
        (∀ x, ¬ OuterSideThickening.IsOuterSideDart T.diagram T.family x) ∧
        (∀ x, ¬ CellSideThickening.IsCellSideDart T.diagram T.family x) ∧
        (∀ x, ¬ CellHairThickening.IsCellHair T.diagram x) ∧ HasCleanTwoGon T)
      (fun T g k hlen hg U hv hT =>
        ⟨CellSideThickening.noOuterSpur_of_step T.diagram g k hlen hg hT.1,
          CellSideThickening.noOuterCellDart_of_step T.diagram g k hlen hg hT.2.1,
          RegionPairThickening.noOuterSideDart_step T.diagram g k hlen hg U hT.2.2.1,
          RegionPairThickening.noCellSideDart_step T.diagram g k hlen hg U hv hT.2.2.2.1,
          RegionPairThickening.noCellHair_step T.diagram g k hlen hg hT.2.2.2.2.1,
          hpairStep hlea T g k hlen hg U hT.2.2.2.2.2⟩)
      S₅ (hvalueOf S₅) ⟨hspur₅, hcell₅, hside₅, hcside₅, hhair₅, hP₅⟩
  obtain ⟨hloops₆, hmulti₆, b₀, hb₀, hbt, P₆, f₆, hf₆, hcorner₆, hcellF₆⟩ := hP₆
  exact ⟨S₆, hloops₆, hmulti₆, b₀, hb₀, hbt, P₆, f₆, hf₆, hcorner₆, hcellF₆,
    fun _ _ _ ha _ hb hab _ _ _ =>
      twoGonCopyCleanAt_of_free hlea S₆ hspur₆ hcell₆ hside₆ hcside₆ hhair₆ hpair₆ ha hb hab⟩

/-- **The clean-copy section leaf from the six step Props.** -/
theorem osinTwoGonCleanCopySection_of_steps
    (hspurStep : TwoGonSpurStepStatement.{u, w, v})
    (hocellStep : TwoGonOuterCellStepStatement.{u, w, v})
    (hosideStep : TwoGonOuterSideStepStatement.{u, w, v})
    (hcsideStep : TwoGonCellSideStepStatement.{u, w, v})
    (hhairStep : TwoGonCellHairStepStatement.{u, w, v})
    (hpairStep : TwoGonRegionPairStepStatement.{u, w, v}) :
    OsinTwoGonCleanCopySectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun rho _ W _ =>
    twoGonCleanCopyInput_of_steps hspurStep hocellStep hosideStep hcsideStep hhairStep
      hpairStep⟩⟩

/-- **C6′, uniformly in the parameters, from the six step Props and the Euler equalities.** -/
theorem osinTwoGonHoldsSection_of_stepsEuler
    (hspurStep : TwoGonSpurStepStatement.{u, w, v})
    (hocellStep : TwoGonOuterCellStepStatement.{u, w, v})
    (hosideStep : TwoGonOuterSideStepStatement.{u, w, v})
    (hcsideStep : TwoGonCellSideStepStatement.{u, w, v})
    (hhairStep : TwoGonCellHairStepStatement.{u, w, v})
    (hpairStep : TwoGonRegionPairStepStatement.{u, w, v})
    (heuler : OsinTwoGonDecompositionEulerSectionStatement.{u, w, v}) :
    OsinTwoGonHoldsSectionStatement.{u, w, v} :=
  osinTwoGonHoldsSection_of_cleanCopyEuler
    (osinTwoGonCleanCopySection_of_steps hspurStep hocellStep hosideStep hcsideStep hhairStep
      hpairStep) heuler

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.twoGonCopyCleanAt_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonCleanCopyInput_of_steps
#audit_axioms GroupApproximation.GGT.VanKampen.osinTwoGonCleanCopySection_of_steps
#audit_axioms GroupApproximation.GGT.VanKampen.osinTwoGonHoldsSection_of_stepsEuler
