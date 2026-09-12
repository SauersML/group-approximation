import GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion

/-! # The inserted edge really lies between G-faces and has the chosen endpoints -/

namespace GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion

open HullSC EdgeInsertion
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (k : Fin (Delta.faceBoundary f).darts.length)
  (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
  (letter : RelLetter G Lambda)
  (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label))

include hf in
theorem inserted_outer :
    (map Delta f k).faceOf (some none) ≠ keep Delta f k Delta.outerFace ∧
    (map Delta f k).faceOf ((map Delta f k).alpha (some none)) ≠ keep Delta f k Delta.outerFace :=
  ⟨(keptFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) k Delta.outerFace hf.symm).symm,
    (keptFace_ne_prefixFace Delta.toCombMap (Delta.faceBoundary f) k Delta.outerFace hf.symm).symm⟩

theorem inserted_cells :
    ∀ C ∈ (diagram Delta f k hf hcells letter hprefix).relatorCells,
      (map Delta f k).faceOf (some none) ≠ C.face ∧
      (map Delta f k).faceOf ((map Delta f k).alpha (some none)) ≠ C.face := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact ⟨(keptFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) k C₀.face (hcells C₀ hC₀)).symm,
    (keptFace_ne_prefixFace Delta.toCombMap (Delta.faceBoundary f) k C₀.face (hcells C₀ hC₀)).symm⟩

theorem label_away_inserted (D : RelGenSet G Lambda) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (d : (map Delta f k).Dart) (ha : d ≠ some none) (hb : d ≠ (map Delta f k).alpha (some none)) :
    D.IsLetter ((diagram Delta f k hf hcells letter hprefix).label d) := by
  change EdgeInsertion.Dart Delta.toCombMap at d
  rcases d with _ | (_ | d)
  · exact (hb rfl).elim
  · exact (ha rfl).elim
  · exact hlabel d

noncomputable abbrev vertexEquiv : (map Delta f k).Vertex ≃ Delta.toCombMap.Vertex :=
  EdgeInsertion.vertexEquiv Delta.toCombMap (firstCorner Delta.toCombMap (Delta.faceBoundary f))
    (secondCorner Delta.toCombMap (Delta.faceBoundary f) k)

theorem vertex_positive :
    vertexEquiv Delta f k ((map Delta f k).vertexOf (some none)) =
      Delta.toCombMap.vertexOf (firstCorner Delta.toCombMap (Delta.faceBoundary f)) := rfl

theorem vertex_negative :
    vertexEquiv Delta f k ((map Delta f k).vertexOf ((map Delta f k).alpha (some none))) =
      Delta.toCombMap.vertexOf (secondCorner Delta.toCombMap (Delta.faceBoundary f) k) := rfl

end GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.inserted_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.label_away_inserted
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.vertex_positive
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.vertex_negative
