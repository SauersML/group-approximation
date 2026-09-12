import GroupApproximation.KunThom.CountingEndgameProps

/-!
# From the one-sided inequalities to concentration

`CompressorRelativeData.concentrated_of_oneSided` is the producer `hmedian` of the
per-compressor assembly
(`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_frameSteps`).  It
applies Kun and Thom's Lemma 4.4 (arXiv:2608.06222v3) in the block form
`MedianVertexForm.blockRatio_negligible`, with

* the compression setup and the ambient expander decomposition of the relative data;
* the objects of the cluster frame as blocks (`ClusterFrame.embedding`), whose
  uncovered mass is negligible (`ClusterFrame.uncovered_negligible`);
* the arrow count as observable (`one_le_observable`);
* the matching and the matched objects of every compressor, with the negligible
  unmatched weight and missing bridge mass of the relative data;
* the one-sided data `κ` and `Bad` supplied by `OneSided`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CompressorNormalizationAssembly

/-- Every object has arrow count at least `1`. -/
theorem one_le_observable {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (i : F.Obj n) : 1 ≤ observable F n i := by
  classical
  unfold observable
  exact ArrowCountMedian.one_le_arrowCount _

namespace CompressorRelativeData

/-- **`hmedian`.**  The one-sided inequalities concentrate (Kun–Thom, Lemma 4.4). -/
theorem concentrated_of_oneSided {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) (h : M.OneSided) : M.Concentrated := by
  classical
  obtain ⟨κ, Bad, hκ, hκv, hone, hbad⟩ := h
  intro η hη hη₂
  refine MedianVertexForm.blockRatio_negligible M.setup A M.ambient M.ambientGenerators_symm
    M.ambientGenerators_generate F.embedding (observable F) (one_le_observable F)
    F.uncovered_negligible M.bridge_self_negligible M.matching M.matched Bad κ hκ hκv hone
    hbad M.unmatched_negligible (fun q hq ↦ (M.bridge_negligible q hq).congr fun n ↦ ?_)
    hη hη₂ t M.mem_compressors
  rw [M.matching_of_mem hq n]

end CompressorRelativeData

end CountingEndgame
end GroupApproximation
