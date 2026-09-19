import GroupApproximation.GGT.VanKampen.SurgeryCutLemma65

/-!
# Quasi-geodesic boundary sections survive the actual region cut

The enclosing walk is written using ambient darts, whereas the cut diagram
uses the retained-dart subtype. Its outer boundary maps to the inverse of the
cut-away region's boundary cycle, in the same order. An exact partition of
that ambient walk therefore lifts to an exact partition of the actual cut
boundary, preserving every section word and both quasi-geodesic constants.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe u w v

private theorem exists_partition_of_map_eq_flatten
    {α β : Type*} (f : α → β) (word : List α) (parts : List (List β))
    (h : word.map f = parts.flatten) :
    ∃ pieces : List (List α), pieces.flatten = word ∧
      pieces.map (List.map f) = parts := by
  induction parts generalizing word with
  | nil =>
      have hw : word = [] := by simpa using h
      exact ⟨[], by simp [hw], rfl⟩
  | cons part parts ih =>
      obtain ⟨first, rest, hword, hfirst, hrest⟩ :=
        List.map_eq_append_iff.mp h
      obtain ⟨pieces, hflatten, hmap⟩ := ih rest hrest
      refine ⟨first :: pieces, ?_, ?_⟩
      · simpa only [List.flatten_cons, hflatten] using hword.symm
      · simp only [List.map_cons, hfirst, hmap]

namespace RegionCutData

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- The actual cut boundary, read in ambient darts, is the inverse of the
cut-away region's ordered boundary. This equality includes its base position. -/
theorem diagram_outerDarts_map_val (cut : RegionCutData Delta) :
    (Embedded.outerDarts cut.diagram).map Subtype.val =
      Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle := by
  have hmap := replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap
    cut.outside cut.region Delta.faceBoundary
  change (((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
    Delta.faceBoundary (newFace Delta.toCombMap cut.outside cut.region)).darts.reverse.map
      (replaceGRegion Delta.toCombMap cut.outside cut.region).alpha).map Subtype.val) = _
  calc
    _ = (((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
        Delta.faceBoundary (newFace Delta.toCombMap cut.outside cut.region)).darts).map
          Subtype.val).reverse.map Delta.toCombMap.alpha := by
      have h : ∀ l : List (KeptDart Delta.toCombMap cut.outside),
          (l.reverse.map (keptAlpha Delta.toCombMap cut.outside)).map Subtype.val =
            (l.map Subtype.val).reverse.map Delta.toCombMap.alpha := by
        intro l
        simp only [List.map_reverse, List.map_map]
        rfl
      exact h _
    _ = _ := by rw [hmap]; rfl

/-- Lift an exact partition of the ambient enclosing walk to the actual
retained-dart boundary. Each lifted section has exactly its ambient word. -/
theorem exists_boundarySections_of_partition
    (cut : RegionCutData Delta) (D : RelGenSet G Lambda) (lambda c : ℝ)
    (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    Nonempty (Embedded.BoundarySections D lambda c cut.diagram) := by
  obtain ⟨pieces, hflatten, hmap⟩ := exists_partition_of_map_eq_flatten
    (α := cut.diagram.toCombMap.Dart)
    (fun d => d.1) (Embedded.outerDarts cut.diagram) parts
    (cut.diagram_outerDarts_map_val.trans hdecomposition)
  have hlength : pieces.length = parts.length := by
    simpa only [List.length_map] using congrArg List.length hmap
  refine ⟨{
    count := pieces.length
    count_pos := hlength.symm ▸ hpos
    count_le := hlength.symm ▸ hle
    part := fun j => pieces[j.val]
    decomposition := ?_
    quasiGeodesic := ?_ }⟩
  · exact ((congrArg List.flatten (List.ofFn_getElem (xs := pieces))).trans
      hflatten).symm
  · intro j
    have hmem : (pieces.get j).map Subtype.val ∈ parts := by
      rw [← hmap]
      exact List.mem_map.mpr ⟨pieces.get j, List.get_mem pieces j, rfl⟩
    have h := hquasi _ hmem
    simp only [Embedded.dartWord, List.map_map, List.get_eq_getElem] at h
    exact h

/-- The cut's original geometric partition supplies the current Lemma 6.5
record. The section field is constructed, with no separate cut-diagram
section certificate required from the caller. -/
theorem exists_lemma65CutData_of_partition
    (cut : RegionCutData Delta) (D : RelGenSet G Lambda) (lambda c : ℝ)
    (hred : Delta.Reduced) (hcells : 0 < cut.diagram.rCellCount)
    (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    Nonempty (Embedded.Lemma65CutData D lambda c Delta) := by
  obtain ⟨sections⟩ := cut.exists_boundarySections_of_partition D lambda c parts
    hpos hle hdecomposition hquasi
  exact ⟨cut.toLemma65CutData D lambda c hred hcells sections⟩

end RegionCutData

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.diagram_outerDarts_map_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.exists_boundarySections_of_partition
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.exists_lemma65CutData_of_partition
