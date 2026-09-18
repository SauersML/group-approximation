import GroupApproximation.Manuscript.NonMF.Full.GL06c.RegionCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoArcSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.RegionProfileTransport
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-arc face set producer at a whole section

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), and `thm:hull` (non_mf_groups_exist.tex,
"Hull's small cancellation theorem", ~2121).  Two distinct exterior regions of one cell `Π` to one
section `q_1` bound, with `Π` and `q_1`, the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.  When
the section spans the whole boundary, the target arc `t_2` of `Γ_1` may be all of `∂Δ`.  Cutting
the first region `Γ_{i,1}` off `Γ_1` (`exists_cut_pocketFaceSet`) leaves a pocket face set whose
source arc misses the source arc of `Γ_{i,1}` on `∂Π` and whose target arc misses its target arc
on `∂Δ`, so both arcs are proper.

* `wholeSectionInput`: `SectionPocketFaceSetWholeSectionTwoArcInput` for all parameters, on the
  clean copy of `PocketFaceSetOnCopy.exists_copyClean` with the kept cell of
  `sectionPocketKeptCell`.
* `wholeSectionTwoArc`: the residual `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`,
  with `ε₀ = 0` and `ρ₀ = 1`.

## Manuscript status

Closes the residual `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` of `thm:hull`
(non_mf_groups_exist.tex) through Osin's Lemma 9.7(b).
-/

namespace GroupApproximation.Full.GL06c

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

universe u w v

/-- **The two-arc face set producer at a whole section** (`thm:hull`, Osin Lemma 9.7(b)).  On the
clean copy, the pocket face set `Γ_1` of two exterior regions of one cell to one section, with the
first region cut off, is a closed walk with proper source and target arcs. -/
theorem wholeSectionInput {G : Type u} [Group G] {Lambda : Type w} (D : GGT.RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (W : Set (List (GGT.RelLetter G Lambda))) :
    SectionPocketFaceSetWholeSectionTwoArcInput.{u, w, v} D lambda c eps W := by
  unfold SectionPocketFaceSetWholeSectionTwoArcInput
  intro Delta cuts hlea S i j a ha b hb hab hja hjb _
  have haS : a ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlen0 := PocketFaceSetOnCopy.one_lt_boundaryWord_length S haS hbS hab hja.1 hjb.1
  obtain ⟨S₄, e, ⟨E⟩, hp, hclean⟩ := PocketFaceSetOnCopy.exists_copyClean
    RegionPairThickening.sectionPocketRegionsCopy hlea S hlen0
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
  have hcyx : K.CopyClean y x := hclean i' y x hy hx hxy'.symm _ _ K hKi
  obtain ⟨kept, hkept'⟩ := sectionPocketKeptCell D lambda c eps W Delta cuts S₄ hlea₄ i' j x y
    hx hy hxy' hjx hjy K hKi hfirst hsecond hgap hstart hend hc
  obtain ⟨P, hPc, hP⟩ := himp hlea₄ hc ⟨kept, hkept'⟩
  obtain ⟨K', hK'⟩ := exists_cut_pocketFaceSet S₄.toRealizedSectionFamily hlea₄ hx hy hxy' hjx
    hjy K hKi hfirst hsecond hgap hstart hend hcyx P hPc hP
  exact ⟨S₄.diagram, ⟨E⟩, S₄.label_admissible, K', hK'⟩

/-- **The residual `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`** (`thm:hull`,
Osin Lemma 9.7(b)), with `ε₀ = 0` and `ρ₀ = 1`: the producer `wholeSectionInput` needs neither the
hyperbolicity of the alphabet nor the small cancellation condition. -/
theorem wholeSectionTwoArc :
    GGT.VanKampen.OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v} := by
  unfold OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement
  intro G _ Lambda D _ lambda c _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ =>
    wholeSectionInput.{u, w, v} D lambda c eps W⟩⟩

end GroupApproximation.Full.GL06c

#audit_axioms GroupApproximation.Full.GL06c.wholeSectionInput
#audit_axioms GroupApproximation.Full.GL06c.wholeSectionTwoArc
