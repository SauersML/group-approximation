import GroupApproximation.GGT.VanKampen.CombMapEdgeKeptFaces

/-! # Literal boundary transport on faces untouched by edge insertion -/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

universe u w

noncomputable def keptFace (M : CombMap.{u}) (a b : M.Dart) (f : M.Face) :
    (toCombMap M a b).Face := (toCombMap M a b).faceOf (embed M f.out)

@[simp] theorem faceMap_keptFace (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) :
    faceMap M a b hface (keptFace M a b f) = f := Quotient.out_eq f

theorem faceOf_embed_eq_keptFace (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (d : M.Dart) (hd : M.faceOf d = f) :
    (toCombMap M a b).faceOf (embed M d) = keptFace M a b f := by
  apply (faceOf_embed_eq_iff M a b hface d f.out (by rwa [hd])).mpr
  exact hd.trans (Quotient.out_eq f).symm

/-- Exactly the embedded old darts constitute the retained face. -/
theorem faceOf_eq_keptFace_iff (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (d : Dart M) :
    (toCombMap M a b).faceOf d = keptFace M a b f ↔
      ∃ e : M.Dart, embed M e = d ∧ M.faceOf e = f := by
  constructor
  · intro h
    have hclass := congrArg (faceMap M a b hface) h
    rw [faceMap_faceOf, faceMap_keptFace] at hclass
    rcases d with _ | (_ | d)
    · exact (hf hclass.symm).elim
    · exact (hf hclass.symm).elim
    · exact ⟨d, rfl, hclass⟩
  · rintro ⟨e, rfl, he⟩
    exact faceOf_embed_eq_keptFace M a b hface f hf e he

theorem mem_keptBoundary_iff (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (B : FaceBoundary M f) (d : Dart M) :
    d ∈ B.darts.map (embed M) ↔ (toCombMap M a b).faceOf d = keptFace M a b f := by
  rw [List.mem_map, faceOf_eq_keptFace_iff M a b hface f hf d]
  constructor
  · rintro ⟨e, he, hed⟩
    exact ⟨e, hed, (B.mem_iff e).mp he⟩
  · rintro ⟨e, hed, he⟩
    exact ⟨e, (B.mem_iff e).mpr he, hed⟩

theorem keptBoundary_chain (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (B : FaceBoundary M f) :
    (B.darts.map (embed M)).IsChain (fun d e : Dart M => (toCombMap M a b).facePerm d = e) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i + 1 < B.darts.length := by simpa only [List.length_map] using hi
  simp only [List.getElem_map]
  rw [facePerm_embed_of_ne M a b _ hface (by
    rw [(B.mem_iff _).mp (List.getElem_mem (by omega))]
    exact hf)]
  exact congrArg (embed M) ((List.isChain_iff_getElem.mp B.chain) i hi')

theorem keptBoundary_nonempty (M : CombMap.{u}) {f : M.Face} (B : FaceBoundary M f) :
    B.darts.map (embed M) ≠ [] := by
  intro h
  exact B.nonempty (List.map_eq_nil_iff.mp h)

theorem keptBoundary_closes (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (B : FaceBoundary M f) :
    (toCombMap M a b).facePerm
      ((B.darts.map (embed M)).getLast (keptBoundary_nonempty M B)) =
        (B.darts.map (embed M)).head (keptBoundary_nonempty M B) := by
  rw [List.getLast_map, List.head_map]
  rw [facePerm_embed_of_ne M a b _ hface (by
    rw [(B.mem_iff _).mp (List.getLast_mem B.nonempty)]
    exact hf), B.closes]

/-- Retain the entire ordered traversal, including its chosen start. -/
noncomputable def keptFaceBoundary (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (B : FaceBoundary M f) : FaceBoundary (toCombMap M a b) (keptFace M a b f) where
  darts := B.darts.map (embed M)
  nonempty := keptBoundary_nonempty M B
  nodup := B.nodup.map (embed_injective M)
  mem_iff := mem_keptBoundary_iff M a b hface f hf B
  chain := keptBoundary_chain M a b hface f hf B
  closes := keptBoundary_closes M a b hface f hf B
  length_eq_degree := Surgery.MapCollapse.length_eq_faceDegree_of_nodup
    (toCombMap M a b) (keptFace M a b f) (B.darts.map (embed M))
    (B.nodup.map (embed_injective M)) (mem_keptBoundary_iff M a b hface f hf B)

/-- Any labels retained on old darts give exactly the old face word. -/
theorem keptFaceBoundary_word (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (f : M.Face) (hf : f ≠ M.faceOf a)
    (B : FaceBoundary M f) {A : Type w} (label : M.Dart → A) (newLabel : Dart M → A)
    (hlabel : ∀ d, newLabel (embed M d) = label d) :
    (keptFaceBoundary M a b hface f hf B).darts.map newLabel = B.darts.map label := by
  change (B.darts.map (embed M)).map newLabel = _
  rw [List.map_map]
  apply List.map_congr_left
  intro d _
  exact hlabel d

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.faceOf_eq_keptFace_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.keptFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.keptFaceBoundary_word
