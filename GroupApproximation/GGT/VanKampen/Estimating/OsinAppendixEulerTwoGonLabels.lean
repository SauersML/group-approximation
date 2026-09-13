import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGon
import GroupApproximation.Meta.AxiomGuard

/-!
# The labels of a two-gon of `Φ'_M` with no corner in its gap

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3: "inside every 2-gon of `Φ'_M`, there is
a vertex of `Φ_M`".  `TwoGonHoldsInput` (`Estimating/OsinAppendixEulerSmallFaces.lean`) asks that
a two-gon of `phiMapO` with no corner in its gap at the outer vertex holds a relator cell.  This
module reads off the labels of such a two-gon, for the pocket argument of
`EmptyTwoGonInput` (`Estimating/OsinAppendixEulerEmptyTwoGon.lean`).

* `exists_outer_of_isTwoGon`: a two-gon has a cell dart `y` at the outer vertex; its region `a`
  and the region `b` two steps on are different exterior regions of one cell, and the face closes
  after four steps;
* `sameSection_of_not_gapHoldsCorner`: when no corner lies in the gap after `a`, the target arc of
  `a` ends before the target arc of `b` starts, and both lie in one section;
* `exists_twoGonLabels`: the labels `i`, `j`, `a`, `b` of `EmptyTwoGonInput`, for a globally
  distinguished system;
* `ExtPhiData.phiRegionO_of_faceOf_eq`: every dart of the two-gon has region `a` or `b`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}

section Generic

variable {Delta : DiscDiagram.{u, w, v} W} {family E : Finset (RegionCandidate D eps Delta)}

/-- **A two-gon has a cell dart at the outer vertex.**  Its region and the region two steps on
are different exterior regions of one cell, and the face closes after four steps. -/
theorem exists_outer_of_isTwoGon (P : ExtPhiData family E)
    (hmulti : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False)
    {f : (phiMapO family E).Face} (hf : (phiSubdividedMultigraphO P).IsTwoGon f) :
    ∃ y : (phiMapO family E).Dart, phiCellSideO y = true ∧ (phiMapO family E).faceOf y = f ∧
      sideCellO (phiRegionO y) (phiSideO y) = none ∧
      (phiMapO family E).facePerm ((phiMapO family E).facePerm
          ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y ∧
      phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) ≠ phiRegionO y ∧
      (phiRegionO y).2.target = none ∧
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))).2.target =
        none ∧
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))).2.source =
        (phiRegionO y).2.source := by
  obtain ⟨d, hd, hface, h4, hR⟩ := hf
  have hdc : phiCellSideO d = true := hd
  obtain ⟨hd2, h1⟩ := sideCellO_facePerm_facePerm P d hdc
  obtain ⟨-, h2⟩ := sideCellO_facePerm_facePerm P _ hd2
  rw [h4] at h2
  obtain ⟨ht, ht2, hsrc⟩ := exterior_of_sideCellO_eq hmulti (phiRegionO_mem d)
    (phiRegionO_mem ((phiMapO family E).facePerm ((phiMapO family E).facePerm d))) hR h1 h2
  cases hs : phiSideO d with
  | false =>
      refine ⟨d, hdc, hface, ?_, h4, hR, ht, ht2, hsrc⟩
      rw [hs]
      exact ht
  | true =>
      refine ⟨(phiMapO family E).facePerm ((phiMapO family E).facePerm d), hd2, ?_, ?_, ?_, ?_,
        ht2, ?_, ?_⟩
      · rw [CombMap.faceOf_facePerm, CombMap.faceOf_facePerm]
        exact hface
      · rw [h1, hs]
        exact ht
      · rw [h4]
      · rw [h4]
        exact Ne.symm hR
      · rw [h4]
        exact ht
      · rw [h4]
        exact hsrc.symm

/-- One step around a face from a cell dart keeps the region. -/
theorem ExtPhiData.phiRegionO_facePerm (P : ExtPhiData family E) (x : (phiMapO family E).Dart)
    (hx : phiCellSideO x = true) :
    phiRegionO ((phiMapO family E).facePerm x) = phiRegionO x := by
  obtain ⟨hr1, -, hc1⟩ := P.phiO_alpha x
  have hc1' : phiCellSideO ((phiMapO family E).alpha x) = false := by simp [hc1, hx]
  exact (P.phiO_sigma_of_midpoint ((phiMapO family E).alpha x) hc1').1.trans hr1

/-- **Every dart of a two-gon has one of its two regions.** -/
theorem ExtPhiData.phiRegionO_of_faceOf_eq (P : ExtPhiData family E)
    {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    {z : (phiMapO family E).Dart}
    (hz : (phiMapO family E).faceOf z = (phiMapO family E).faceOf y) :
    phiRegionO z = phiRegionO y ∨
      phiRegionO z = phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) := by
  have hy2 := (sideCellO_facePerm_facePerm P y hy).1
  have hmem : ∀ n : ℕ, ((phiMapO family E).facePerm ^ n) y = y ∨
      ((phiMapO family E).facePerm ^ n) y = (phiMapO family E).facePerm y ∨
      ((phiMapO family E).facePerm ^ n) y =
        (phiMapO family E).facePerm ((phiMapO family E).facePerm y) ∨
      ((phiMapO family E).facePerm ^ n) y = (phiMapO family E).facePerm
        ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) := by
    intro n
    induction n with
    | zero => exact Or.inl (by rw [pow_zero, Equiv.Perm.one_apply])
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h | h | h <;> rw [h]
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inl h4
  obtain ⟨n, hn⟩ := (((phiMapO family E).faceOf_eq_iff y z).mp hz.symm).exists_nat_pow_eq
  rcases hmem n with h | h | h | h <;> rw [h] at hn <;> subst hn
  · exact Or.inl rfl
  · exact Or.inl (P.phiRegionO_facePerm y hy)
  · exact Or.inr rfl
  · exact Or.inr (P.phiRegionO_facePerm _ hy2)

end Generic

section Sections

variable {Delta : DiscDiagram.{u, w, v} W}

/-- **No corner in the gap puts both regions in one section, `a` first.** -/
theorem sameSection_of_not_gapHoldsCorner {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) {a b : RegionCandidate D eps Delta}
    (hja : ∃ j, TargetsSectionIndex cuts j a) (hjb : ∃ j, TargetsSectionIndex cuts j b)
    (hpos : 0 < a.2.targetArc.length) (h : ∀ k, ¬GapHoldsCorner cuts a b k) :
    a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1 ∧
      ∃ j, TargetsSectionIndex cuts j a ∧ TargetsSectionIndex cuts j b := by
  obtain ⟨ja, hja⟩ := hja
  obtain ⟨jb, hjb⟩ := hjb
  have hle : a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1 := by
    by_contra hlt
    apply h jb
    rw [GapHoldsCorner, if_neg hlt]
    exact Or.inr hjb.2.1
  refine ⟨hle, ja, hja, ?_⟩
  rcases lt_trichotomy ja jb with hlt | rfl | hgt
  · exfalso
    apply h jb
    rw [GapHoldsCorner, if_pos hle]
    exact ⟨le_trans hja.2.2 (cuts.cut_mono (Fin.succ_le_castSucc_iff.mpr hlt)), hjb.2.1⟩
  · exact hjb
  · exfalso
    have h1 := hjb.2.2
    have h2 := cuts.cut_mono (Fin.succ_le_castSucc_iff.mpr hgt)
    have h3 := hja.2.1
    omega

/-- A selected region to the boundary is an exterior region of its source cell. -/
theorem mem_exteriorAt_of_mem {selected : Finset (RegionCandidate D eps Delta)}
    {a : RegionCandidate D eps Delta} (ha : a ∈ selected) (ht : a.2.target = none) :
    a ∈ exteriorAt selected a.2.source := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
  show a.2.target.isSome = false
  simp [ht]

end Sections

/-- **The labels of a two-gon with no corner in its gap.**  For a globally distinguished system
with no multiple edges, a two-gon of `phiMapO` with no corner in its gap at the outer vertex has a
cell dart `y` at the outer vertex.  Its region `a` and the region `b` two steps on are different
exterior regions of one cell to one section `j`, and the target arc of `a` ends before the target
arc of `b` starts. -/
theorem exists_twoGonLabels {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hmulti : S.NoMultipleEdges)
    {E : Finset (RegionCandidate D eps S.diagram)} (P : ExtPhiData S.family E)
    {f : (phiMapO S.family E).Face} (hf : (phiSubdividedMultigraphO P).IsTwoGon f)
    (hcorner : ¬GapAtOHoldsCorner cuts S.family E f) :
    ∃ y : (phiMapO S.family E).Dart, phiCellSideO y = true ∧
      (phiMapO S.family E).faceOf y = f ∧ sideCellO (phiRegionO y) (phiSideO y) = none ∧
      (phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm
          ((phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm y))) = y ∧
      ∃ j : Fin cuts.count,
        phiRegionO y ∈ exteriorAt S.family (phiRegionO y).2.source ∧
        phiRegionO ((phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm y)) ∈
          exteriorAt S.family (phiRegionO y).2.source ∧
        phiRegionO y ≠
          phiRegionO ((phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm y)) ∧
        TargetsSectionIndex cuts j (phiRegionO y) ∧
        TargetsSectionIndex cuts j
          (phiRegionO ((phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm y))) ∧
        (phiRegionO y).2.targetArc.start.1 + (phiRegionO y).2.targetArc.length ≤
          (phiRegionO ((phiMapO S.family E).facePerm
            ((phiMapO S.family E).facePerm y))).2.targetArc.start.1 := by
  have hmultiE : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin S.diagram.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False :=
    fun a ha b hb hab => hmulti a (P.subset ha) b (P.subset hb) hab
  obtain ⟨y, hyc, hyf, hyO, h4, hR, ht, ht2, hsrc⟩ := exists_outer_of_isTwoGon P hmultiE hf
  have hya := P.subset (phiRegionO_mem y)
  have hyb := P.subset
    (phiRegionO_mem ((phiMapO S.family E).facePerm ((phiMapO S.family E).facePerm y)))
  obtain ⟨hle, j, hja, hjb⟩ := sameSection_of_not_gapHoldsCorner cuts
    (S.respects _ hya ht) (S.respects _ hyb ht2) (S.nondegenerate _ hya).2
    (fun k hk => hcorner ⟨y, hyf, hyc, hyO, k, hk⟩)
  refine ⟨y, hyc, hyf, hyO, h4, j, mem_exteriorAt_of_mem hya ht, ?_, Ne.symm hR, hja, hjb, hle⟩
  rw [← hsrc]
  exact mem_exteriorAt_of_mem hyb ht2

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_outer_of_isTwoGon
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.phiRegionO_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.phiRegionO_of_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sameSection_of_not_gapHoldsCorner
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_exteriorAt_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_twoGonLabels
