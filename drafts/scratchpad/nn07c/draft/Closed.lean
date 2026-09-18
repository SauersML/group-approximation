import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFree.FFF.FromPrintedData
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly

/-!
# Existence of the Fournier-Facio configuration (unconditional)

`non_mf_group_notes.tex`, Theorem `thm:torsionfree`, l.2767-2775, uses the group
`G_0` of `[FFF, Section 2]` (F. Fournier-Facio, arXiv:2608.02025 v2, §2).
The printed paragraph of `non_mf_groups_exist.tex` l.835-843 is proved by
`TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger`, which takes
the relative Greendlinger lemma (Osin, Lemma 4.4) as input. That lemma is
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero`.
`exists_notesConfiguration_of_printedData` then turns the result into a notes
configuration.
-/

namespace GroupApproximation.Full.NN07c

/-- `thm:torsionfree` (`non_mf_group_notes.tex`, l.2767-2775): the notes
configuration exists. Its group `G_0` is finitely generated and
acylindrically hyperbolic. -/
theorem exists_notesConfiguration :
    ∃ C : GroupApproximation.Full.NN07b.NotesConfiguration,
      Group.FG C.G₀ ∧
        GroupApproximation.Manuscript.NonMF.TorsionFree.IsAcylindricallyHyperbolic C.G₀ := by
  obtain ⟨G₀, _, _, htf, hT, hacyl, F, hFT, -, -⟩ :=
    GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger
      GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero
  exact exists_notesConfiguration_of_printedData htf hT hacyl F hFT

end GroupApproximation.Full.NN07c
