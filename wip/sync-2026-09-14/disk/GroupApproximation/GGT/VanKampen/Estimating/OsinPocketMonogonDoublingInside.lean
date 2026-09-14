import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoublingStrip
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingInside
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across the doubling of a monogon inside it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A vertex splitting inside a pinched pocket face set
(`PocketFaceSet.exists_pinchStep_of_inside`) merges two corners of the face set, and both must be
G-faces.  `PocketFaceSet.faceEdgeDoublingInside` fills the corner of a relator face of the face set
with at least two darts.  When that face is a monogon `[d]`, the doubling of its edge
(`MonogonDoubling.diagram`) puts a G-cell digon `[some none, d]` in the corner.  The new face set
holds the image faces and the digon (`MonogonDoubling.faceSet`), so its boundary darts are the old
ones and the pocket face set transports by the dart embedding, with the same walk order and the same
repeated visits.

* `MonogonDoubling.isBoundaryDart_faceSet_iff_map` and `MonogonDoubling.faceSetBoundaryCycle`: the
  boundary darts and the boundary cycle of a face set holding the monogon, after the doubling.
* `MonogonDoubling.vertexOf_alpha_embedding_eq_iff` and `MonogonDoubling.label_letter`: vertices
  and letter labels across the doubling.
* `PocketFaceSet.monogonDoublingInside`: the transported pocket face set.
* `PocketFaceSet.monogonDoublingInside_closedWalk` and `monogonDoublingInside_repeatedVisits`: walk
  order and repeated visits are unchanged.
* `PocketFaceSet.exists_pinchStep_of_monogonDoublingInside`: the conclusion of
  `exists_pinchStep_of_inside` for a split of the doubled diagram, back on the old diagram.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace MonogonDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)

/-- **The boundary of a face set holding the monogon, after the doubling, is the old boundary.** -/
theorem isBoundaryDart_faceSet_iff_map {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    {l : List Delta.toCombMap.Dart}
    (hB : ∀ e, Surgery.MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ l)
    (x : (map Delta f).Dart) :
    Surgery.MapCollapse.IsBoundaryDart (map Delta f) (faceSet Delta f S) x ↔
      x ∈ l.map (EdgeInsertion.embed Delta.toCombMap) := by
  rcases x with _ | (_ | e)
  · refine iff_of_false (fun h => h.2 (faceOf_some_none_mem Delta f S)) (fun h => ?_)
    obtain ⟨e, _, he⟩ := List.mem_map.mp h
    cases he
  · refine iff_of_false (fun h => h.2 (faceOf_alpha_some_none_mem Delta f hS)) (fun h => ?_)
    obtain ⟨e, _, he⟩ := List.mem_map.mp h
    cases he
  · refine (isBoundaryDart_embed_iff Delta f hS e).trans ((hB e).trans ?_)
    refine ⟨fun h => List.mem_map.mpr ⟨e, h, rfl⟩, fun h => ?_⟩
    obtain ⟨e', he', hee'⟩ := List.mem_map.mp h
    rwa [← EdgeInsertion.embed_injective Delta.toCombMap hee']

variable (hf : f ≠ Delta.outerFace) (hmono : (Delta.faceBoundary f).darts.length = 1)

/-- **The boundary cycle of a face set holding the monogon, after the doubling**: the old cycle,
mapped by the dart embedding. -/
noncomputable def faceSetBoundaryCycle {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap S) :
    Surgery.MapCollapse.BoundaryCycle (diagram Delta f hf hmono).toCombMap
      (faceSet Delta f S) where
  cycle := B.cycle.map (embedding Delta f hf hmono).darts
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := B.cycle_nodup.map (embedding Delta f hf hmono).darts.injective
  cycle_mem_iff x :=
    (isBoundaryDart_faceSet_iff_map Delta f hS (fun e => (B.cycle_mem_iff e).symm) x).symm

theorem faceSetBoundaryCycle_cycle {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap S) :
    (faceSetBoundaryCycle Delta f hf hmono hS B).cycle =
      B.cycle.map (embedding Delta f hf hmono).darts :=
  rfl

/-- **A relator cell away from the monogon keeps its darts**, indexed through the cell map. -/
theorem cellDarts_indexEquiv {i : Fin Delta.rCellCount} (hi : (Embedded.cell Delta i).face ≠ f) :
    Embedded.cellDarts (diagram Delta f hf hmono) ((cellMap Delta f hf hmono).indexEquiv i) =
      (Embedded.cellDarts Delta i).map (embedding Delta f hf hmono).darts :=
  cellDarts_cellIndex Delta f hf hmono hi

/-- **The doubling keeps the vertices of old darts.** -/
theorem vertexOf_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta f hf hmono).toCombMap.vertexOf ((embedding Delta f hf hmono).darts x) =
        (diagram Delta f hf hmono).toCombMap.vertexOf ((embedding Delta f hf hmono).darts y) ↔
      Delta.toCombMap.vertexOf x = Delta.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff Delta.toCombMap
    (EdgeInsertion.firstCorner Delta.toCombMap (Delta.faceBoundary f))
    (EdgeInsertion.secondCorner Delta.toCombMap (Delta.faceBoundary f) (zero Delta f)) x y

/-- **The doubling keeps the vertices of old darts and their reverses.** -/
theorem vertexOf_alpha_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta f hf hmono).toCombMap.vertexOf
        ((diagram Delta f hf hmono).toCombMap.alpha ((embedding Delta f hf hmono).darts x)) =
        (diagram Delta f hf hmono).toCombMap.vertexOf ((embedding Delta f hf hmono).darts y) ↔
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha x) = Delta.toCombMap.vertexOf y := by
  rw [(embedding Delta f hf hmono).alpha]
  exact vertexOf_embedding_eq_iff Delta f hf hmono _ y

/-- **The doubling keeps letter labels** of the symmetrized alphabet. -/
theorem label_letter {D : RelGenSet G Lambda}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (d : (diagram Delta f hf hmono).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((diagram Delta f hf hmono).label d) :=
  label_admissible Delta f hf hmono (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) hlabel d

end MonogonDoubling

namespace PocketFaceSet

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The pocket face set across the doubling of a monogon** `f` inside the face set: the image
faces with the new digon, the same cells, and the boundary cycle, the arcs and the sides mapped by
the dart embedding. -/
noncomputable def monogonDoublingInside (K : PocketFaceSet D eps X lo hi)
    (f : X.toCombMap.Face) (hf : f ≠ X.outerFace) (hmono : (X.faceBoundary f).darts.length = 1)
    (hs : f ∈ K.faces) :
    PocketFaceSet D eps (MonogonDoubling.diagram X f hf hmono) lo hi where
  faces := MonogonDoubling.faceSet X f K.faces
  outerFace_not_mem :=
    MonogonDoubling.outerFace_not_mem_faceSet X f hf hmono K.outerFace_not_mem
  source := (MonogonDoubling.cellMap X f hf hmono).indexEquiv K.source
  source_not_mem := by
    rw [(MonogonDoubling.cellMap X f hf hmono).indexed_cell K.source,
      (MonogonDoubling.cellMap X f hf hmono).face_eq]
    exact fun h => K.source_not_mem ((MonogonDoubling.mem_faceSet_faceImage X f K.faces _).mp h)
  kept := (MonogonDoubling.cellMap X f hf hmono).indexEquiv K.kept
  kept_mem := by
    rw [(MonogonDoubling.cellMap X f hf hmono).indexed_cell K.kept,
      (MonogonDoubling.cellMap X f hf hmono).face_eq]
    exact (MonogonDoubling.mem_faceSet_faceImage X f K.faces _).mpr K.kept_mem
  sourceArc := K.sourceArc.mapTo (MonogonDoubling.embedding X f hf hmono).darts
    (MonogonDoubling.cellDarts_indexEquiv X f hf hmono (K.source_face_ne hs))
  targetArc := K.targetArc.mapTo (MonogonDoubling.embedding X f hf hmono).darts
    ((MonogonDoubling.embedding X f hf hmono).outerDarts_eq hf)
  firstSide := K.firstSide.map (MonogonDoubling.embedding X f hf hmono).darts
  secondSide := K.secondSide.map (MonogonDoubling.embedding X f hf hmono).darts
  boundary := MonogonDoubling.faceSetBoundaryCycle X f hf hmono hs K.boundary
  decomposition := by
    rw [CyclicArc.mapTo_darts, CyclicArc.mapTo_darts, DiscEmbeddingAway.invDarts_map,
      MonogonDoubling.faceSetBoundaryCycle_cycle, K.decomposition]
    simp only [List.map_append]
  firstSide_length_le := by
    rw [List.length_map]
    exact K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_map]
    exact K.secondSide_length_le
  firstSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.firstSide_norm_le
  secondSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.secondSide_norm_le
  lo_le := by
    rw [CyclicArc.mapTo_start]
    exact K.lo_le
  le_hi := by
    rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
    exact K.le_hi

variable (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face) (hf : f ≠ X.outerFace)
  (hmono : (X.faceBoundary f).darts.length = 1) (hs : f ∈ K.faces)

theorem monogonDoublingInside_faces :
    (K.monogonDoublingInside f hf hmono hs).faces = MonogonDoubling.faceSet X f K.faces :=
  rfl

theorem monogonDoublingInside_boundary_cycle :
    (K.monogonDoublingInside f hf hmono hs).boundary.cycle =
      K.boundary.cycle.map (MonogonDoubling.embedding X f hf hmono).darts :=
  rfl

/-- **The doubling keeps walk order.** -/
theorem monogonDoublingInside_closedWalk (hK : K.ClosedWalk) :
    (K.monogonDoublingInside f hf hmono hs).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (MonogonDoubling.embedding X f hf hmono).darts).IsChain
      (fun d e => (MonogonDoubling.diagram X f hf hmono).toCombMap.vertexOf
        ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha d) =
          (MonogonDoubling.diagram X f hf hmono).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (MonogonDoubling.vertexOf_alpha_embedding_eq_iff X f hf hmono d e).mpr h)
  · change (MonogonDoubling.diagram X f hf hmono).toCombMap.vertexOf
        ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha
          ((K.boundary.cycle.map (MonogonDoubling.embedding X f hf hmono).darts).getLast
            (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty)) =
      (MonogonDoubling.diagram X f hf hmono).toCombMap.vertexOf
        ((K.boundary.cycle.map (MonogonDoubling.embedding X f hf hmono).darts).head
          (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (MonogonDoubling.vertexOf_alpha_embedding_eq_iff X f hf hmono _ _).mpr hK.2

/-- **The doubling keeps the repeated visits.** -/
theorem monogonDoublingInside_repeatedVisits :
    (K.monogonDoublingInside f hf hmono hs).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [monogonDoublingInside_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((MonogonDoubling.diagram X f hf hmono).toCombMap.vertexOf ∘
      (MonogonDoubling.embedding X f hf hmono).darts)
    X.toCombMap.vertexOf
    (fun a b => MonogonDoubling.vertexOf_embedding_eq_iff X f hf hmono a b) _

/-- **A pinch step through the doubling of a monogon inside the face set.**  A vertex splitting of
the doubled diagram inside the transported face set, with turns along vertex rotation and two
boundary darts on the new vertices, gives the conclusion of `exists_pinchStep_of_inside` for the
old diagram. -/
theorem exists_pinchStep_of_monogonDoublingInside
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (I : PinchSplit.Input (MonogonDoubling.diagram X f hf hmono))
    (hI : I.Inside (K.monogonDoublingInside f hf hmono hs).faces)
    (hchain : (K.monogonDoublingInside f hf hmono hs).boundary.cycle.IsChain fun d e =>
      I.StretchAvoids ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha d) e ∨
        I.StretchAvoids e ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha d))
    (hcloses :
      I.StretchAvoids ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha
          ((K.monogonDoublingInside f hf hmono hs).boundary.cycle.getLast
            (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty))
          ((K.monogonDoublingInside f hf hmono hs).boundary.cycle.head
            (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty) ∨
        I.StretchAvoids ((K.monogonDoublingInside f hf hmono hs).boundary.cycle.head
            (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty)
          ((MonogonDoubling.diagram X f hf hmono).toCombMap.alpha
            ((K.monogonDoublingInside f hf hmono hs).boundary.cycle.getLast
              (K.monogonDoublingInside f hf hmono hs).boundary.cycle_nonempty)))
    {e₁ e₂ : (MonogonDoubling.diagram X f hf hmono).toCombMap.Dart}
    (he₁ : e₁ ∈ (K.monogonDoublingInside f hf hmono hs).boundary.cycle)
    (he₂ : e₂ ∈ (K.monogonDoublingInside f hf hmono hs).boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨X', K', ⟨hequiv⟩, hlabel', hwalk, hlt⟩ :=
    (K.monogonDoublingInside f hf hmono hs).exists_pinchStep_of_inside
      (MonogonDoubling.label_letter X f hf hmono hlabel) I hI hchain hcloses he₁ he₂ hx hy
  exact ⟨X', K', ⟨(MonogonDoubling.oEquivalent X f hf hmono).trans hequiv⟩, hlabel', hwalk,
    lt_of_lt_of_eq hlt (K.monogonDoublingInside_repeatedVisits f hf hmono hs)⟩

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.isBoundaryDart_faceSet_iff_map
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.faceSetBoundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.vertexOf_alpha_embedding_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.label_letter
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.monogonDoublingInside
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.monogonDoublingInside_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.monogonDoublingInside_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_pinchStep_of_monogonDoublingInside
