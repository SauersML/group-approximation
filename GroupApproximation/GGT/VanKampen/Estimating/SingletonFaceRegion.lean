import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.SingletonFaceBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A single G-face read as a contiguity region

The contradiction step of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3, Case 1
of its proof), and the merges in the proof of Lemma 9.7(a), produce a NEW
`ε`-contiguity subdiagram: after the connector words are inserted across a G-face,
the quadrilateral face bounded by a source-cell arc, a short side, a target arc and
a short side is itself the region.  This file is the constructor for that region.

A G-face `f` with no internally paired dart (`Surgery.MapCollapse.NoInternalFaceDart`)
has its stored face cycle as the boundary of the singleton face set
(`FaceSetBoundary.ofSingleton`), and the one-face shelling
`Embedded.shelling_oneFace` pastes it.  So once the cycle, read from a suitable base,
decomposes as `sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts ++ leftSide`
with both sides short, every field of `ContiguityGeometry` is supplied
(`ContiguityGeometry.ofSingletonFace`).  The region candidate it defines is compatible
with every region avoiding `f`, is not a member of any family avoiding `f`, and adds
its arc weight to such a family (`cons_ofSingletonFace_pairwise`,
`familyWeight_cons_ofSingletonFace`).  That is the shape of the contradiction with
`weight_maximal` of a distinguished family.

No distinct-cell or O52 datum is involved: the output is an unrestricted
`RegionCandidate`, as the Definition-9.2 selection of the section statements uses.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open WordMetric HullSC
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **The boundary of a single G-face.**  With no dart of `f` paired to another dart
of `f`, every dart of the stored face cycle is a boundary dart of `{f}`, consecutive
darts follow the face permutation, and the cycle closes. -/
noncomputable def FaceSetBoundary.ofSingleton {Delta : DiscDiagram.{u, w, v} W}
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hval : RelLetter.listVal (Delta.faceWord f) = 1)
    (hno : Surgery.MapCollapse.NoInternalFaceDart Delta.toCombMap f) :
    FaceSetBoundary Delta ({f} : Finset Delta.toCombMap.Face) where
  faces_nonempty := Finset.singleton_nonempty f
  all_gCells := by
    intro face hface
    rw [Finset.mem_singleton.mp hface]
    exact ⟨hf, hval⟩
  cycle := (Delta.faceBoundary f).darts
  cycle_nonempty := (Delta.faceBoundary f).nonempty
  cycle_nodup := (Delta.faceBoundary f).nodup
  cycle_mem_iff := by
    intro d
    rw [(Delta.faceBoundary f).mem_iff]
    constructor
    · intro hd
      exact ⟨Finset.mem_singleton.mpr hd, fun h => hno d hd (Finset.mem_singleton.mp h)⟩
    · intro hd
      exact Finset.mem_singleton.mp hd.1
  cycle_chain := by
    have hmem : ∀ d ∈ (Delta.faceBoundary f).darts,
        IsBoundaryDart Delta ({f} : Finset Delta.toCombMap.Face) d := by
      intro d hd
      have hdf := ((Delta.faceBoundary f).mem_iff d).mp hd
      exact ⟨Finset.mem_singleton.mpr hdf, fun h => hno d hdf (Finset.mem_singleton.mp h)⟩
    rw [List.isChain_iff_getElem]
    intro i hi
    have hstep : Delta.toCombMap.facePerm (Delta.faceBoundary f).darts[i] =
        (Delta.faceBoundary f).darts[i + 1] :=
      (List.isChain_iff_getElem.mp (Delta.faceBoundary f).chain) i hi
    refine ⟨hmem _ (List.getElem_mem _), hmem _ (List.getElem_mem _), ?_⟩
    exact hstep ▸ Relation.ReflTransGen.refl
  cycle_closes := by
    have hmem : ∀ d ∈ (Delta.faceBoundary f).darts,
        IsBoundaryDart Delta ({f} : Finset Delta.toCombMap.Face) d := by
      intro d hd
      have hdf := ((Delta.faceBoundary f).mem_iff d).mp hd
      exact ⟨Finset.mem_singleton.mpr hdf, fun h => hno d hdf (Finset.mem_singleton.mp h)⟩
    refine ⟨hmem _ (List.getLast_mem _), hmem _ (List.head_mem _), ?_⟩
    exact (Delta.faceBoundary f).closes ▸ Relation.ReflTransGen.refl

@[simp] theorem FaceSetBoundary.ofSingleton_cycle {Delta : DiscDiagram.{u, w, v} W}
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hval : RelLetter.listVal (Delta.faceWord f) = 1)
    (hno : Surgery.MapCollapse.NoInternalFaceDart Delta.toCombMap f) :
    (FaceSetBoundary.ofSingleton f hf hval hno).cycle = (Delta.faceBoundary f).darts :=
  rfl

/-- **A single G-face as a contiguity region.**  The face cycle, rotated to base `k`,
reads the reversed source arc, a short right side, the target arc as it occurs on a
region boundary, and a short left side. -/
noncomputable def ContiguityGeometry.ofSingletonFace {D : RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hval : RelLetter.listVal (Delta.faceWord f) = 1)
    (hno : Surgery.MapCollapse.NoInternalFaceDart Delta.toCombMap f) (k : ℕ)
    (source : Fin Delta.rCellCount) (target : Option (Fin Delta.rCellCount))
    (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (targetDarts Delta target))
    (rightSide leftSide : List Delta.toCombMap.Dart)
    (hdecomp : (Delta.faceBoundary f).darts.rotate k =
      sourceArc.reverseDarts ++ rightSide ++
        targetBoundaryDarts Delta target targetArc ++ leftSide)
    (hright : rightSide.length ≤ eps) (hleft : leftSide.length ≤ eps)
    (hrightNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Delta rightSide)) ≤ eps)
    (hleftNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Delta leftSide)) ≤ eps) :
    ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face) where
  boundary := (FaceSetBoundary.ofSingleton f hf hval hno).rotate k
  source := source
  target := target
  sourceArc := sourceArc
  targetArc := targetArc
  rightSide := rightSide
  leftSide := leftSide
  boundary_decomposition := hdecomp
  rightSide_length_le := hright
  leftSide_length_le := hleft
  rightSide_norm_le := hrightNorm
  leftSide_norm_le := hleftNorm
  pasting := ⟨[f], shelling_oneFace (Finset.mem_singleton_self f) k⟩

namespace RegionCandidate

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {f : Delta.toCombMap.Face}

/-- A singleton region at `f` is compatible with every region avoiding `f`. -/
theorem compatible_singleton_of_not_mem
    (H : ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face))
    (a : RegionCandidate D eps Delta) (ha : f ∉ a.1) :
    Compatible (⟨{f}, H⟩ : RegionCandidate D eps Delta) a :=
  Finset.disjoint_singleton_left.mpr ha

/-- A singleton region at `f` is not a member of a family avoiding `f`. -/
theorem singleton_not_mem_of_avoid
    (H : ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face))
    {family : Finset (RegionCandidate D eps Delta)} (havoid : ∀ a ∈ family, f ∉ a.1) :
    (⟨{f}, H⟩ : RegionCandidate D eps Delta) ∉ family :=
  fun h => havoid _ h (Finset.mem_singleton_self f)

/-- Adjoining the singleton region to a compatible family avoiding `f` keeps the
family pairwise compatible. -/
theorem cons_singleton_pairwise
    (H : ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face))
    {family : Finset (RegionCandidate D eps Delta)} (havoid : ∀ a ∈ family, f ∉ a.1)
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family) :
    EstimatingSelection.PairwiseCompatible Compatible
      (Finset.cons ⟨{f}, H⟩ family (singleton_not_mem_of_avoid H havoid)) := by
  intro a ha b hb hab
  rcases Finset.mem_cons.mp ha with rfl | ha'
  · rcases Finset.mem_cons.mp hb with rfl | hb'
    · exact (hab rfl).elim
    · exact compatible_singleton_of_not_mem H b (havoid b hb')
  · rcases Finset.mem_cons.mp hb with rfl | hb'
    · exact Disjoint.symm (compatible_singleton_of_not_mem H a (havoid a ha'))
    · exact hpairwise a ha' b hb' hab

/-- Adjoining the singleton region adds exactly its two arc lengths to the family
weight. -/
theorem familyWeight_cons_singleton
    (H : ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face))
    {family : Finset (RegionCandidate D eps Delta)} (havoid : ∀ a ∈ family, f ∉ a.1) :
    EstimatingSelection.familyWeight weight
        (Finset.cons ⟨{f}, H⟩ family (singleton_not_mem_of_avoid H havoid)) =
      (H.sourceArc.length + H.targetArc.length) +
        EstimatingSelection.familyWeight weight family :=
  Finset.sum_cons (singleton_not_mem_of_avoid H havoid)

/-- A singleton region with a nonempty source arc strictly increases the weight of
any family avoiding its face. -/
theorem familyWeight_lt_cons_singleton
    (H : ContiguityGeometry D eps Delta ({f} : Finset Delta.toCombMap.Face))
    {family : Finset (RegionCandidate D eps Delta)} (havoid : ∀ a ∈ family, f ∉ a.1)
    (hsource : 0 < H.sourceArc.length) :
    EstimatingSelection.familyWeight weight family <
      EstimatingSelection.familyWeight weight
        (Finset.cons ⟨{f}, H⟩ family (singleton_not_mem_of_avoid H havoid)) := by
  rw [familyWeight_cons_singleton H havoid]
  omega

end RegionCandidate
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.ofSingleton
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.ofSingletonFace
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.cons_singleton_pairwise
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.familyWeight_cons_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.familyWeight_lt_cons_singleton
