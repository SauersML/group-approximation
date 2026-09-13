import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickeningSix
import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickeningPreserves
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopySideCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.RegionProfileTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The face set between two exterior regions, on a clean copy

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This module assembles `SectionPocketFaceSetInput`, and with it the waist residual
`OsinSectionPocketFaceSetSectionStatement`, from two named residuals.

1. **The copy.** A distinguished section family over a least-area diagram passes to an O-equivalent
   family satisfying the edge conditions `PocketWalk.CopyClean` for every pair of distinct exterior
   regions of one cell.  The thickenings run in this order:
   * the exterior (`OuterSideThickening.outerSideThickening`): no outer spur, no edge between a
     relator cell and the exterior, no exterior edge across a side;
   * relator faces across sides (`CellSideThickening.cellSideThickeningPreserving`);
   * relator self-edges (`CellHairThickening.cellHairSidesThickening`);
   * edges between two selected regions: the named residual `SectionPocketRegionsCopyStatement`.
   `exists_copyClean` composes them and builds the six fields.
2. **The kept cell.** `SectionPocketKeptCellStatement`: the pocket walk of two distinct exterior
   regions of one cell to one section has a relator cell on its side.  This is Osin's argument that
   a pocket without an `R`-cell merges the two regions.  It replaces the hypothesis that the outer
   cycle of the walk follows its boundary: that hypothesis fails when the two sides touch at a
   vertex (the lake, `Estimating/OsinPocketLakeModel`, Configuration B), and the edge conditions do
   not exclude such a touch.

Then `PocketWalk.exists_pocketFaceSet_of_exteriorAt` turns the walk on the copy into a pocket face
set in walk order (`sectionPocketFaceSetInput_of_residuals`).  The copy needs a boundary word of
length at least two, which two distinct exterior regions force (`one_lt_boundaryWord_length`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

/-- **Edges between two selected regions, thickened** (not proved here; the `regions` stage of the
copy).  A distinguished section family over a boundary word of length at least two, with no relator
word of value one and none of the defects removed by the earlier stages, has a distinguished section
family over the same cuts on an O-equivalent diagram that keeps all of that and has no edge from a
face of one selected region to a face of another.  Its regions correspond to the old ones with the
same weight, target profiles and source indices. -/
def SectionPocketRegionsCopyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    1 < Delta.boundaryWord.length →
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) →
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) →
            (∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x) →
              (∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x) →
                (∀ x, ¬ CellHairThickening.IsCellHair S.diagram x) →
                  ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
                    (e : S.family ≃ S'.family),
                    Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
                      (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                      (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
                      (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
                      (∀ x, ¬ OuterSideThickening.IsOuterSideDart S'.diagram S'.family x) ∧
                      (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
                      (∀ x, ¬ CellHairThickening.IsCellHair S'.diagram x) ∧
                      (∀ x ∈ S'.family, ∀ y ∈ S'.family, x ≠ y → ∀ d,
                        S'.diagram.toCombMap.faceOf d ∈ x.1 →
                          S'.diagram.toCombMap.faceOf (S'.diagram.toCombMap.alpha d) ∉ y.1) ∧
                      S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                      ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                        (e a).1.2.source.val = a.1.2.source.val

/-- **The kept relator cell of the pocket** (not proved here).  On a least-area diagram, the pocket
walk `s_1 t_1 s_2 t_2` of two distinct exterior regions of one cell to one section, in the shape of
`PocketWalk.exists_of_exteriorAt`, satisfying the edge conditions, has a relator cell on its side.
Osin: a pocket without an `R`-cell merges the two regions, against the choice of the family. -/
def SectionPocketKeptCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count)
        (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
                K.source = i → K.firstSide = y.2.leftSide → K.secondSide = x.2.rightSide →
                  (∃ Gap : CyclicArc (cellDarts S.diagram i),
                    K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++
                      y.2.sourceArc.darts) →
                    K.targetArc.start.1 = x.2.targetArc.start.1 →
                      K.targetArc.start.1 + K.targetArc.length =
                          y.2.targetArc.start.1 + y.2.targetArc.length →
                        K.CopyClean x y →
                          ∃ kept : Fin S.diagram.rCellCount,
                            (cell S.diagram kept).face ∈
                              sideFaces S.diagram.toCombMap K.walk

namespace PocketFaceSetOnCopy

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- A dart of the target arc of a region to the boundary lies on a face of the region. -/
theorem faceOf_mem_of_mem_targetArc {X : DiscDiagram.{u, w, v} W} (a : RegionCandidate D eps X)
    (ht : a.2.target = none) {d : X.toCombMap.Dart} (hd : d ∈ a.2.targetArc.darts) :
    X.toCombMap.faceOf d ∈ a.1 := by
  have hcarrier : d ∈ targetDarts X a.2.target := a.2.targetArc.mem_cycle_of_mem_darts hd
  rw [ht] at hcarrier
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hcarrier
  have houter : X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
    rw [← hed, X.toCombMap.alpha_involutive e]
    exact ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)
  rcases FaceEdgeDoubling.mem_targetBoundaryDarts_of_mem X a.2.target a.2.targetArc hd with h | h
  · have hcycle : d ∈ a.2.boundary.cycle := by
      rw [a.2.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ h)
    exact ((a.2.boundary.cycle_mem_iff d).mp hcycle).1
  · have hcycle : X.toCombMap.alpha d ∈ a.2.boundary.cycle := by
      rw [a.2.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ h)
    have hin := ((a.2.boundary.cycle_mem_iff _).mp hcycle).1
    rw [houter] at hin
    exact (OuterSpurThickening.outer_not_mem X a.2 hin).elim

/-- **Two distinct regions to the boundary force a boundary word of length at least two**: with
at most one exterior dart, both target arcs hold it, and its face lies in both regions. -/
theorem one_lt_boundaryWord_length (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a b : RegionCandidate D eps S.diagram} (haS : a ∈ S.family) (hbS : b ∈ S.family)
    (hab : a ≠ b) (hta : a.2.target = none) (htb : b.2.target = none) :
    1 < Delta.boundaryWord.length := by
  by_contra hlt
  have hle : Delta.boundaryWord.length ≤ 1 := Nat.not_lt.mp hlt
  have hout : (outerDarts S.diagram).length = Delta.boundaryWord.length := by
    rw [← S.equiv.boundaryWord_eq, S.diagram.boundaryWord_length, ← S.diagram.faceWord_length]
    simp only [outerDarts, DiscDiagram.faceWord, List.length_map, List.length_reverse]
  obtain ⟨da, hda⟩ := List.exists_mem_of_length_pos
    (by rw [a.2.targetArc.darts_length]; exact (S.nondegenerate a haS).2)
  obtain ⟨db, hdb⟩ := List.exists_mem_of_length_pos
    (by rw [b.2.targetArc.darts_length]; exact (S.nondegenerate b hbS).2)
  have hca : da ∈ outerDarts S.diagram := by
    have h := a.2.targetArc.mem_cycle_of_mem_darts hda
    rw [hta] at h
    exact h
  have hcb : db ∈ outerDarts S.diagram := by
    have h := b.2.targetArc.mem_cycle_of_mem_darts hdb
    rw [htb] at h
    exact h
  have hdd : da = db :=
    CellSideThickening.eq_of_mem_of_length_le_one (by rw [hout]; exact hle) hca hcb
  have hfa := faceOf_mem_of_mem_targetArc a hta hda
  have hfb := faceOf_mem_of_mem_targetArc b htb hdb
  rw [← hdd] at hfb
  exact Finset.disjoint_left.mp (S.pairwise a haS b hbS hab) hfa hfb

/-- **The clean copy.**  From the `regions` stage, a distinguished section family over a least-area
diagram with a boundary word of length at least two has an O-equivalent distinguished family, with
the same target profiles and source indices, whose every pocket walk of two distinct exterior
regions of one cell satisfies the edge conditions. -/
theorem exists_copyClean (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hlea : Delta.LeastArea) (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlen0 : 1 < Delta.boundaryWord.length) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
          (e a).1.2.source.val = a.1.2.source.val) ∧
        ∀ (i : Fin S'.diagram.rCellCount) (x y : RegionCandidate D eps S'.diagram),
          x ∈ RegionCandidate.exteriorAt S'.family i →
            y ∈ RegionCandidate.exteriorAt S'.family i → x ≠ y →
              ∀ (lo hi : ℕ) (K : PocketWalk D eps S'.diagram lo hi), K.source = i →
                K.CopyClean x y := by
  have hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 := fun C hC =>
    DiscDiagram.leastArea_listVal_word_ne_one
      (OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea) C hC
  obtain ⟨S₁, e₁, ⟨E₁⟩, hspur₁, hcell₁, hside₁, hvalue₁, -, hp₁⟩ :=
    OuterSideThickening.outerSideThickening D lambda c eps W Delta cuts S hlen0 hvalue
  obtain ⟨S₂, e₂, ⟨E₂⟩, -, hcs₂, hspur₂, hcell₂, hside₂, hvalue₂, -, hp₂⟩ :=
    CellSideThickening.cellSideThickeningPreserving D lambda c eps W Delta cuts S₁ hlen0 hvalue₁
      hspur₁ hcell₁ hside₁
  obtain ⟨S₃, e₃, ⟨E₃⟩, hvalue₃, hspur₃, hcell₃, hside₃, hcs₃, hhair₃, -, hp₃⟩ :=
    CellHairThickening.cellHairSidesThickening D lambda c eps W Delta cuts S₂ hlen0 hvalue₂
      hspur₂ hcell₂ hside₂ hcs₂
  obtain ⟨S₄, e₄, ⟨E₄⟩, -, hspur₄, hcell₄, hside₄, hcs₄, hhair₄, hreg₄, -, hp₄⟩ :=
    hregions D lambda c eps W Delta cuts S₃ hlen0 hvalue₃ hspur₃ hcell₃ hside₃ hcs₃ hhair₃
  refine ⟨S₄, e₁.trans (e₂.trans (e₃.trans e₄)), ⟨E₁.trans (E₂.trans (E₃.trans E₄))⟩,
    fun a => ?_, fun i x y hx hy hxy lo hi K hKi => ?_⟩
  · obtain ⟨p₄, s₄⟩ := hp₄ (e₃ (e₂ (e₁ a)))
    obtain ⟨p₃, s₃⟩ := hp₃ (e₂ (e₁ a))
    obtain ⟨p₂, s₂⟩ := hp₂ (e₁ a)
    obtain ⟨p₁, s₁⟩ := hp₁ a
    exact ⟨p₄.trans (p₃.trans (p₂.trans p₁)), s₄.trans (s₃.trans (s₂.trans s₁))⟩
  · have hxS : x ∈ S₄.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hyS : y ∈ S₄.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
    have hlea₄ : S₄.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S₄.equiv hlea
    refine ⟨OuterCellThickening.spur_of_noOuterSpur hspur₄, ?_, ?_, hreg₄ x hxS y hyS hxy, ?_,
      OuterSideThickening.side_outer_of_noOuterSideDart hside₄ hxS hyS⟩
    · rw [hKi]
      exact CellHairThickening.cell_self_of_noCellHair hhair₄ i
    · rw [hKi]
      exact OuterCellThickening.cell_outer_of_noOuterCellDart hcell₄ i
    · rw [hKi]
      exact CellSideThickening.side_cell_of_noCellSideDart S₄ hcs₄ hlea₄ hx hy hxy

end PocketFaceSetOnCopy

/-- **The face set between two exterior regions, from the two residuals.** -/
theorem sectionPocketFaceSetInput_of_residuals
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hkept : SectionPocketKeptCellStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetInput.{u, w, v} D lambda c eps W := by
  unfold SectionPocketFaceSetInput
  intro Delta cuts hlea S i j a ha b hb hab hja hjb
  have haS : a ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlen0 := PocketFaceSetOnCopy.one_lt_boundaryWord_length S haS hbS hab hja.1 hjb.1
  obtain ⟨S₄, e, ⟨E⟩, hp, hclean⟩ := PocketFaceSetOnCopy.exists_copyClean hregions hlea S hlen0
  obtain ⟨i', a', b', -, ha', hb', hab', hja', hjb'⟩ :=
    RegionProfileTransport.exists_exteriorPair e hp ha hb hab hja hjb
  obtain ⟨K, x, y, hxy, hKi, hfirst, hsecond, hgap, hstart, hend, himp⟩ :=
    PocketWalk.exists_pocketFaceSet_of_exteriorAt S₄.toRealizedSectionFamily ha' hb' hab' hja' hjb'
  obtain ⟨hx, hy, hxy', hjx, hjy⟩ : x ∈ RegionCandidate.exteriorAt S₄.family i' ∧
      y ∈ RegionCandidate.exteriorAt S₄.family i' ∧ x ≠ y ∧
        RegionCandidate.TargetsSectionIndex cuts j x ∧
          RegionCandidate.TargetsSectionIndex cuts j y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha', hb', hab', hja', hjb'⟩
    · exact ⟨hb', ha', hab'.symm, hjb', hja'⟩
  have hlea₄ : S₄.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S₄.equiv hlea
  have hc : K.CopyClean x y := hclean i' x y hx hy hxy' _ _ K hKi
  obtain ⟨kept, hkept'⟩ := hkept D lambda c eps W Delta cuts S₄ hlea₄ i' j x y hx hy hxy' hjx hjy
    K hKi hfirst hsecond hgap hstart hend hc
  obtain ⟨P, -, hP⟩ := himp hlea₄ hc ⟨kept, hkept'⟩
  exact ⟨S₄.diagram, ⟨E⟩, S₄.label_admissible, P, hP⟩

/-- **The waist residual `OsinSectionPocketFaceSetSectionStatement`, from the two residuals**,
with `ε₀ = 0` and `ρ₀ = 1`. -/
theorem osinSectionPocketFaceSetSection_of_residuals
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hkept : SectionPocketKeptCellStatement.{u, w, v}) :
    OsinSectionPocketFaceSetSectionStatement.{u, w, v} := by
  unfold OsinSectionPocketFaceSetSectionStatement
  intro G _ Lambda D _ lambda c _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ =>
    sectionPocketFaceSetInput_of_residuals hregions hkept D lambda c eps W⟩⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketRegionsCopyStatement
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketKeptCellStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSetOnCopy.faceOf_mem_of_mem_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSetOnCopy.one_lt_boundaryWord_length
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSetOnCopy.exists_copyClean
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketFaceSetInput_of_residuals
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketFaceSetSection_of_residuals
