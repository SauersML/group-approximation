import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketInnerWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoArcBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-arc face set producer through the inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.
At a section spanning the whole boundary the target arc of the outer pocket walk can be all of `∂Δ`
(`Estimating/OsinPocketWholeSectionWrapModel.lean`).  The inner pocket between the two regions keeps both
arcs proper (`Estimating/OsinPocketInnerWalk.lean`, model `Estimating/OsinPocketInnerWalkModel.lean`), so
it gives the below two-arc producer at every section, and in particular the whole-section residual
`SectionPocketFaceSetWholeSectionTwoArcBelowInput` (`Estimating/OsinPocketTwoArcBelow.lean`).

Inner residuals, for two exterior regions `x`, `y` of one cell to one section of a least-area family, with
the inner data of `PocketWalk.exists_inner_of_le` and the edge conditions `PocketWalk.CopyClean` in both
orders (the inner sides are the reversed right side of `y` and left side of `x`):
* `SectionPocketInnerKeptCellStatement`: a relator cell lies on the side of the inner pocket walk, the
  analogue of `SectionPocketKeptCellStatement`;
* `SectionPocketInnerWalkNoncrossingStatement`: the inner pocket walk is noncrossing, the analogue of
  `PocketWalk.noncrossing_of_copyClean`;
* `SectionPocketInnerWalkEulerStatement`: both reclosings of the inner pocket walk keep the Euler
  characteristic, the analogue of `SectionPocketWalkEulerStatement`;
* `SectionPocketInnerEmptyArcsBelowStatement`: when the gap or the inner target arc is empty, under clause
  (b) of Lemma 9.7 below the number of relator cells of `Δ`, the two-arc conclusion.

Assembly: `sectionPocketFaceSetTwoArcBelowInput_of_inner`,
`sectionPocketFaceSetWholeSectionTwoArcBelowInput_of_inner` and
`osinSectionPocketFaceSetWholeSectionTwoArcBelowSection_of_inner`, from the `regions` stage of the copy,
the inner kept cell, the inner noncrossing statement and the empty-arcs residual.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

/-- **The kept relator cell of the inner pocket** (not proved here).  On a least-area diagram, for two
distinct exterior regions `x`, `y` of one cell to one section, with a gap `Gap` between their source arcs
and an arc `t_2` of `∂Δ` from the end of `x`'s target arc to the start of `y`'s, both nonempty, and the
edge conditions in both orders, a relator cell lies on the side of the inner pocket walk. -/
def SectionPocketInnerKeptCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ (Gap T : CyclicArc (cellDarts S.diagram i)) (t₂ : CyclicArc (outerDarts S.diagram)),
                T.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts →
                  t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length →
                    t₂.start.1 + t₂.length = y.2.targetArc.start.1 →
                      ∀ (hGap : 0 < Gap.length) (ht₂ : 0 < t₂.length)
                        (hlo : cuts.cut j.castSucc ≤ t₂.start.1)
                        (hhi : t₂.start.1 + t₂.length ≤ cuts.cut j.succ),
                        (∀ (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi), K.source = i →
                          K.CopyClean x y ∧ K.CopyClean y x) →
                          ∃ kept : Fin S.diagram.rCellCount,
                            (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap
                              (PocketWalk.ofInner i x y Gap t₂ hGap ht₂ hlo hhi).walk

/-- **The inner pocket walk is noncrossing** (not proved here), under the premises of
`SectionPocketInnerKeptCellStatement`. -/
def SectionPocketInnerWalkNoncrossingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ (Gap T : CyclicArc (cellDarts S.diagram i)) (t₂ : CyclicArc (outerDarts S.diagram)),
                T.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts →
                  t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length →
                    t₂.start.1 + t₂.length = y.2.targetArc.start.1 →
                      ∀ (hGap : 0 < Gap.length) (ht₂ : 0 < t₂.length)
                        (hlo : cuts.cut j.castSucc ≤ t₂.start.1)
                        (hhi : t₂.start.1 + t₂.length ≤ cuts.cut j.succ),
                        (∀ (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi), K.source = i →
                          K.CopyClean x y ∧ K.CopyClean y x) →
                          IsNoncrossingClosedWalk S.diagram.toCombMap
                            (PocketWalk.ofInner i x y Gap t₂ hGap ht₂ hlo hhi).walk

/-- **The Euler equalities of the inner pocket walk** (not proved here), under the premises of
`SectionPocketInnerKeptCellStatement`: both reclosings of the noncrossing inner walk keep the Euler
characteristic of the map. -/
def SectionPocketInnerWalkEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ (Gap T : CyclicArc (cellDarts S.diagram i)) (t₂ : CyclicArc (outerDarts S.diagram)),
                T.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts →
                  t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length →
                    t₂.start.1 + t₂.length = y.2.targetArc.start.1 →
                      ∀ (hGap : 0 < Gap.length) (ht₂ : 0 < t₂.length)
                        (hlo : cuts.cut j.castSucc ≤ t₂.start.1)
                        (hhi : t₂.start.1 + t₂.length ≤ cuts.cut j.succ),
                        (∀ (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi), K.source = i →
                          K.CopyClean x y ∧ K.CopyClean y x) →
                          ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap
                              (PocketWalk.ofInner i x y Gap t₂ hGap ht₂ hlo hhi).walk,
                            (reclosedMap S.diagram.toCombMap
                                (sideFaces S.diagram.toCombMap
                                  (PocketWalk.ofInner i x y Gap t₂ hGap ht₂ hlo hhi).walk)
                                (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic ∧
                              (reclosedMap S.diagram.toCombMap
                                  (sideOutside S.diagram.toCombMap
                                    (PocketWalk.ofInner i x y Gap t₂ hGap ht₂ hlo hhi).walk)
                                  (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic

/-- **An empty inner arc, below the inductive bound** (not proved here).  For two distinct exterior
regions of one cell to one section of a least-area diagram, with inner data whose gap or target arc is
empty, the edge conditions in both orders, and clause (b) of Lemma 9.7 below the number of relator cells
of `Δ`, the conclusion of `SectionPocketFaceSetTwoArcBelowInput`. -/
def SectionPocketInnerEmptyArcsBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ (Gap T : CyclicArc (cellDarts S.diagram i)) (t₂ : CyclicArc (outerDarts S.diagram)),
                T.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts →
                  t₂.start.1 = x.2.targetArc.start.1 + x.2.targetArc.length →
                    t₂.start.1 + t₂.length = y.2.targetArc.start.1 →
                      (Gap.length = 0 ∨ t₂.length = 0) →
                        (∀ (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi), K.source = i →
                          K.CopyClean x y ∧ K.CopyClean y x) →
                          ∃ X' : DiscDiagram.{u, w, v} W,
                            Nonempty (OEquivalentDiscDiagram S.diagram X') ∧
                              (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                              ∃ K : PocketFaceSet D eps X' (cuts.cut j.castSucc) (cuts.cut j.succ),
                                K.ClosedWalk ∧ K.sourceArc.length < (cellDarts X' K.source).length ∧
                                  K.targetArc.length < (outerDarts X').length

section Assembly

/-- **The below two-arc producer through the inner pocket.**  Pass to the clean copy, order the two
regions by their target arcs, and take the inner data.  With both inner arcs nonempty the inner pocket
walk is noncrossing with a relator cell on its side, so it gives a pocket face set in walk order whose
arcs are the gap and the arc between the two target arcs, both proper.  Otherwise the empty-arcs residual
applies on the copy. -/
theorem sectionPocketFaceSetTwoArcBelowInput_of_inner
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hkept : SectionPocketInnerKeptCellStatement.{u, w, v})
    (hnoncrossing : SectionPocketInnerWalkNoncrossingStatement.{u, w, v})
    (hempty : SectionPocketInnerEmptyArcsBelowStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetTwoArcBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S i j a ha b hb hab hja hjb
  have haS : a ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlen0 := PocketFaceSetOnCopy.one_lt_boundaryWord_length S haS hbS hab hja.1 hjb.1
  obtain ⟨S₄, e, ⟨E⟩, hp, hclean⟩ := PocketFaceSetOnCopy.exists_copyClean hregions hlea S hlen0
  obtain ⟨i', a', b', -, ha', hb', hab', hja', hjb'⟩ :=
    RegionProfileTransport.exists_exteriorPair e hp ha hb hab hja hjb
  have hlea₄ : S₄.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S₄.equiv hlea
  obtain ⟨x, y, hx, hy, hxy, hjx, hjy, hle⟩ : ∃ x y : RegionCandidate D eps S₄.diagram,
      x ∈ RegionCandidate.exteriorAt S₄.family i' ∧ y ∈ RegionCandidate.exteriorAt S₄.family i' ∧
        x ≠ y ∧ RegionCandidate.TargetsSectionIndex cuts j x ∧
          RegionCandidate.TargetsSectionIndex cuts j y ∧
            x.2.targetArc.start.1 ≤ y.2.targetArc.start.1 := by
    rcases le_total a'.2.targetArc.start.1 b'.2.targetArc.start.1 with h | h
    · exact ⟨a', b', ha', hb', hab', hja', hjb', h⟩
    · exact ⟨b', a', hb', ha', hab'.symm, hjb', hja', h⟩
  have hc : ∀ (lo hi : ℕ) (K : PocketWalk D eps S₄.diagram lo hi), K.source = i' →
      K.CopyClean x y ∧ K.CopyClean y x := fun lo hi K hKi =>
    ⟨hclean i' x y hx hy hxy lo hi K hKi, hclean i' y x hy hx hxy.symm lo hi K hKi⟩
  obtain ⟨Gap, T, t₂, hT, hGaplt, hs, he, ht₂lt, hlo, hhi⟩ :=
    PocketWalk.exists_inner_of_le S₄.toRealizedSectionFamily hx hy hxy hjx hjy hle
  by_cases hpos : 0 < Gap.length ∧ 0 < t₂.length
  · obtain ⟨hGap, ht₂⟩ := hpos
    have hw := hnoncrossing D lambda c eps W Delta cuts S₄ hlea₄ i' j x y hx hy hxy hjx hjy Gap T t₂
      hT hs he hGap ht₂ hlo hhi hc
    obtain ⟨kept, hkept'⟩ := hkept D lambda c eps W Delta cuts S₄ hlea₄ i' j x y hx hy hxy hjx hjy
      Gap T t₂ hT hs he hGap ht₂ hlo hhi hc
    exact ⟨S₄.diagram, ⟨E⟩, S₄.label_admissible,
      (PocketWalk.ofInner i' x y Gap t₂ hGap ht₂ hlo hhi).toPocketFaceSetOfNoncrossing kept hw hkept',
      PocketWalk.toPocketFaceSetOfNoncrossing_closedWalk _ kept hw hkept', hGaplt, ht₂lt⟩
  · have hzero : Gap.length = 0 ∨ t₂.length = 0 := by
      by_contra hne
      push_neg at hne
      exact hpos ⟨Nat.pos_of_ne_zero hne.1, Nat.pos_of_ne_zero hne.2⟩
    obtain ⟨X', ⟨E'⟩, hlabel, K, hK⟩ := hempty D lambda c mu eps W Delta cuts hlea hbelow S₄ i' j x y
      hx hy hxy hjx hjy Gap T t₂ hT hs he hzero hc
    exact ⟨X', ⟨E.trans E'⟩, hlabel, K, hK⟩

/-- **The below whole-section residual through the inner pocket.**  The inner route does not use that
the section spans the whole boundary. -/
theorem sectionPocketFaceSetWholeSectionTwoArcBelowInput_of_inner
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hkept : SectionPocketInnerKeptCellStatement.{u, w, v})
    (hnoncrossing : SectionPocketInnerWalkNoncrossingStatement.{u, w, v})
    (hempty : SectionPocketInnerEmptyArcsBelowStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetWholeSectionTwoArcBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea hbelow S i j a ha b hb hab hja hjb _ =>
    sectionPocketFaceSetTwoArcBelowInput_of_inner hregions hkept hnoncrossing hempty D lambda c mu eps
      W Delta cuts hlea hbelow S i j a ha b hb hab hja hjb

/-- **The uniform below whole-section residual through the inner pocket**, with `ε₀ = 0` and
`ρ₀ = 1`. -/
theorem osinSectionPocketFaceSetWholeSectionTwoArcBelowSection_of_inner
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (hkept : SectionPocketInnerKeptCellStatement.{u, w, v})
    (hnoncrossing : SectionPocketInnerWalkNoncrossingStatement.{u, w, v})
    (hempty : SectionPocketInnerEmptyArcsBelowStatement.{u, w, v}) :
    OsinSectionPocketFaceSetWholeSectionTwoArcBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ =>
    sectionPocketFaceSetWholeSectionTwoArcBelowInput_of_inner hregions hkept hnoncrossing hempty D
      lambda c mu eps W⟩⟩

end Assembly

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketInnerKeptCellStatement
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketInnerWalkEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketInnerEmptyArcsBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketFaceSetTwoArcBelowInput_of_inner
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketFaceSetWholeSectionTwoArcBelowSection_of_inner
