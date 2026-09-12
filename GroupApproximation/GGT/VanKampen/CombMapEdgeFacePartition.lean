import GroupApproximation.GGT.VanKampen.CombMapEdgeSplitBoundary

/-! # Every new face is one split piece or an untouched old face -/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

universe u
variable (M : CombMap.{u}) {f : M.Face} (B : FaceBoundary M f)

noncomputable abbrev prefixFace (k : Fin B.darts.length) := (splitMap M B k).faceOf none
noncomputable abbrev suffixFace (k : Fin B.darts.length) := (splitMap M B k).faceOf (some none)

theorem firstCorner_face : M.faceOf (firstCorner M B) = f :=
  (B.mem_iff _).mp (List.get_mem _ _)

theorem prefixFace_ne_suffixFace (k : Fin B.darts.length) :
    prefixFace M B k ≠ suffixFace M B k := by
  intro h
  have hmem := ((prefixBoundary M B k).mem_iff (some none)).mpr h.symm
  change some none ∈ none :: (B.darts.take k.val).map (embed M) at hmem
  rcases List.mem_cons.mp hmem with hmem | hmem
  · cases hmem
  · obtain ⟨d, _, hd⟩ := List.mem_map.mp hmem
    cases hd

theorem keptFace_injective (a b : M.Dart) (hface : M.faceOf a = M.faceOf b) :
    Function.Injective (keptFace M a b) := by
  intro g h heq
  have hmap := congrArg (faceMap M a b hface) heq
  simpa only [faceMap_keptFace] using hmap

theorem keptFace_ne_prefixFace (k : Fin B.darts.length) (g : M.Face) (hg : g ≠ f) :
    keptFace M (firstCorner M B) (secondCorner M B k) g ≠ prefixFace M B k := by
  intro h
  have hmap := congrArg
    (faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k)) h
  rw [faceMap_keptFace] at hmap
  exact hg (hmap.trans (firstCorner_face M B))

theorem keptFace_ne_suffixFace (k : Fin B.darts.length) (g : M.Face) (hg : g ≠ f) :
    keptFace M (firstCorner M B) (secondCorner M B k) g ≠ suffixFace M B k := by
  intro h
  have hmap := congrArg
    (faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k)) h
  rw [faceMap_keptFace] at hmap
  exact hg (hmap.trans (firstCorner_face M B))

theorem face_partition (k : Fin B.darts.length) (F : (splitMap M B k).Face) :
    F = prefixFace M B k ∨ F = suffixFace M B k ∨
      ∃ g : M.Face, g ≠ f ∧ F = keptFace M (firstCorner M B) (secondCorner M B k) g := by
  refine Quotient.inductionOn' F ?_
  intro d
  rcases d with _ | (_ | d)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · by_cases hd : M.faceOf d = f
    · have hmem : d ∈ B.darts.take k.val ++ B.darts.drop k.val := by
        rw [List.take_append_drop]
        exact (B.mem_iff d).mpr hd
      rcases List.mem_append.mp hmem with hpre | hsuf
      · left
        exact ((prefixBoundary M B k).mem_iff (embed M d)).mp
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hpre, rfl⟩))
      · right; left
        exact ((suffixBoundary M B k).mem_iff (embed M d)).mp
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hsuf, rfl⟩))
    · right; right
      refine ⟨M.faceOf d, hd, ?_⟩
      exact faceOf_embed_eq_keptFace M _ _ (corners_face_eq M B k) _
        (by rwa [firstCorner_face M B]) d rfl

theorem remainingFace (k : Fin B.darts.length) (F : (splitMap M B k).Face)
    (hpre : F ≠ prefixFace M B k) (hsuf : F ≠ suffixFace M B k) :
    let g := faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k) F
    g ≠ f ∧ F = keptFace M (firstCorner M B) (secondCorner M B k) g := by
  rcases face_partition M B k F with h | h | ⟨g, hg, rfl⟩
  · exact (hpre h).elim
  · exact (hsuf h).elim
  · dsimp only
    rw [faceMap_keptFace]
    exact ⟨hg, rfl⟩

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.prefixFace_ne_suffixFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.face_partition
