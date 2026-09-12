import GroupApproximation.GGT.VanKampen.GFaceSplitFaces
import GroupApproximation.GGT.VanKampen.GFaceCornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidateTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a G-face between two prescribed corners

`GFaceWordInsertion.exists_split_output_of_reversible` inserts a word between the FIRST
corner of a G-face and the corner at index `k`, and records the two sides.  The surgery
of Osin's Appendix Lemma 9.4 Case 1 inserts connector words between arbitrary corners,
so this file rebases the face at the chosen start corner first (`GFaceRebase`), exactly
as the landed `exists_corner_output` does, and restates the two sides against the
ORIGINAL traversal:

* the prefix side reads the reversed path, then the arc of the old traversal from
  `start` of length `forwardOffset start finish` (`prefixSide_darts_original`);
* the suffix side reads the path, then the rest of the rotated traversal
  (`suffixSide_darts_original`).

A compatible family of region candidates avoiding the face survives with its card and
weight, and none of its regions contains either side (`retained_regionFamily`).
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded EdgeInsertion
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- A split insertion between two prescribed corners of `f`. -/
abbrev SplitCornerOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (start finish : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) :=
  SplitOutput D (GFaceRebase.diagram Delta f start.val hf hcells) f
    (GFaceRebase.cornerIndex Delta f hf hcells start finish) word

theorem rebased_darts (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face) (n : ℕ)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f) :
    ((GFaceRebase.diagram Delta f n hf hcells).faceBoundary f).darts =
      (Delta.faceBoundary f).darts.rotate n := by
  change (GFaceRebase.boundary Delta f n f).darts = _
  simp only [GFaceRebase.boundary, ite_true, FaceBoundary.rotate]

/-- **The producer** between prescribed corners. -/
theorem exists_split_corner_output (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (start finish : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l))
    (hvalue : RelLetter.listVal word = RelLetter.listVal
      ((((Delta.faceBoundary f).darts.rotate start.val).take
        ((Delta.faceBoundary f).forwardOffset start finish)).map Delta.label)) :
    Nonempty (SplitCornerOutput D Delta f hf hcells start finish word) := by
  apply exists_split_output_of_reversible D
    (GFaceRebase.diagram Delta f start.val hf hcells) hlabel f
    (GFaceRebase.cornerIndex Delta f hf hcells start finish) hf hcells word hne hword hinv
  simpa only [GFaceRebase.diagram, GFaceRebase.boundary, ite_true, GFaceRebase.cornerIndex,
    FaceBoundary.rotate] using hvalue

namespace SplitCornerOutput

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
  {f : Delta.toCombMap.Face} {hf : f ≠ Delta.outerFace}
  {hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f}
  {start finish : Fin (Delta.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)} (R : SplitCornerOutput D Delta f hf hcells start finish word)

/-- The prefix side, against the original traversal of `f`. -/
theorem prefixSide_darts_original :
    (R.diagram.faceBoundary R.prefixSide).darts =
      invDarts R.diagram R.darts ++
        (((Delta.faceBoundary f).darts.rotate start.val).take
          ((Delta.faceBoundary f).forwardOffset start finish)).map R.embedding.darts :=
  R.prefixSide_darts.trans (congrArg
    (fun l : List Delta.toCombMap.Dart => invDarts R.diagram R.darts ++
      (l.take ((Delta.faceBoundary f).forwardOffset start finish)).map R.embedding.darts)
    (rebased_darts Delta f start.val hf hcells))

/-- The suffix side, against the original traversal of `f`. -/
theorem suffixSide_darts_original :
    (R.diagram.faceBoundary R.suffixSide).darts =
      R.darts ++
        (((Delta.faceBoundary f).darts.rotate start.val).drop
          ((Delta.faceBoundary f).forwardOffset start finish)).map R.embedding.darts :=
  R.suffixSide_darts.trans (congrArg
    (fun l : List Delta.toCombMap.Dart => R.darts ++
      (l.drop ((Delta.faceBoundary f).forwardOffset start finish)).map R.embedding.darts)
    (rebased_darts Delta f start.val hf hcells))

/-- **Retention**: a compatible family of region candidates avoiding `f` survives the
insertion with its card and weight, and none of its regions contains either side. -/
theorem retained_regionFamily (metric : RelGenSet G Lambda) (eps : ℕ)
    (family : Finset (RegionCandidate metric eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hpairwise : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    ∃ family' : Finset (RegionCandidate metric eps R.diagram),
      EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family' ∧
      family'.card = family.card ∧
      EstimatingSelection.familyWeight RegionCandidate.weight family' =
        EstimatingSelection.familyWeight RegionCandidate.weight family ∧
      ∀ a ∈ family', R.prefixSide ∉ a.1 ∧ R.suffixSide ∉ a.1 := by
  let E := CornerOutput.originalEmbedding R.toCellOutput
  let C := CornerOutput.originalCellMap R.toCellOutput
  refine ⟨E.regionFamily C hcells hf family havoid,
    E.regionFamily_pairwise C hcells hf family havoid hpairwise,
    E.regionFamily_card C hcells hf family havoid,
    E.regionFamily_weight C hcells hf family havoid, ?_⟩
  intro a ha
  obtain ⟨b, hb, hab⟩ := E.regionFamily_faces C hcells hf family havoid ha
  rw [hab]
  constructor
  · intro hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R.prefixSide_not_kept g (fun h => havoid b hb (h ▸ hg)) hgeq
  · intro hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R.suffixSide_not_kept g (fun h => havoid b hb (h ▸ hg)) hgeq

end SplitCornerOutput
end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_split_corner_output
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitCornerOutput.prefixSide_darts_original
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitCornerOutput.retained_regionFamily
