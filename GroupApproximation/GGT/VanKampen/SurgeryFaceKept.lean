import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.SurgeryFacePartition

/-!
# Boundaries of the faces kept by a region collapse

`Surgery.MapCollapse.replaceGRegion` keeps every dart based outside the
selected region, and `SurgeryFacePartition` identifies the faces of the result
with the old faces outside the region together with one new face.  This file
transports an ordered face boundary across that identification.

For a face `f` outside the region, the retained darts of an ordered boundary of
`f` form an ordered boundary of the face `keptFace` of the replacement, and the
two lists agree after forgetting the retained-dart proofs.  So the face word of
a kept face is unchanged by the collapse.

The two rotation rules used throughout say that face rotation after reclosing
acts by the old face rotation on darts based outside the region, and by the
boundary rotation on darts based inside it.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe v

/-! ## Retained darts based outside the region -/

/-- A dart based outside the region is retained. -/
def keptDartOfNotMem (M : CombMap.{v}) (faces : Finset M.Face) (d : M.Dart)
    (hd : M.faceOf d ∉ faces) : KeptDart M faces := by
  refine ⟨d, ?_⟩
  intro hinternal
  exact hd hinternal.1

theorem keptDartOfNotMem_val (M : CombMap.{v}) (faces : Finset M.Face)
    (d : M.Dart) (hd : M.faceOf d ∉ faces) :
    (keptDartOfNotMem M faces d hd).1 = d := rfl

/-! ## Face rotation after reclosing -/

/-- On a dart based outside the region, the reclosed face rotation is the old
face rotation. -/
theorem replaceGRegion_facePerm_val_of_notMem (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∉ faces) :
    ((replaceGRegion M faces region).facePerm d).1 = M.facePerm d.1 := by
  have hbase : ((replaceGRegion M faces region).facePerm d).1 =
      ((keptSplitEquiv M faces).symm
        (Equiv.sumCongr (outsideFacePerm M faces)
          region.toBoundaryCycle.boundaryPerm
          (keptSplitEquiv M faces d))).1 :=
    congrArg (fun p : Equiv.Perm (KeptDart M faces) => (p d).1)
      (replaceGRegion_facePerm_eq M faces region)
  rw [keptSplitEquiv_apply_of_notMem M faces d hd] at hbase
  exact hbase

/-- On a dart based inside the region, the reclosed face rotation is the
boundary rotation. -/
theorem replaceGRegion_facePerm_val_of_mem (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∈ faces) :
    ((replaceGRegion M faces region).facePerm d).1 =
      (region.toBoundaryCycle.boundaryPerm
        ⟨d.1, isBoundaryDart_of_mem M faces d hd⟩).1 := by
  have hbase : ((replaceGRegion M faces region).facePerm d).1 =
      ((keptSplitEquiv M faces).symm
        (Equiv.sumCongr (outsideFacePerm M faces)
          region.toBoundaryCycle.boundaryPerm
          (keptSplitEquiv M faces d))).1 :=
    congrArg (fun p : Equiv.Perm (KeptDart M faces) => (p d).1)
      (replaceGRegion_facePerm_eq M faces region)
  rw [keptSplitEquiv_apply_of_mem M faces d hd] at hbase
  exact hbase

/-! ## Length of an ordered face enumeration -/

/-- A duplicate-free list containing exactly the darts of one face has the
length of that face's degree. -/
theorem length_eq_faceDegree_of_nodup (N : CombMap.{v}) (g : N.Face)
    (l : List N.Dart) (hnodup : l.Nodup)
    (hmem : ∀ d : N.Dart, d ∈ l ↔ N.faceOf d = g) :
    l.length = N.faceDegree g := by
  classical
  have e₁ : Fin l.length ≃ {x : N.Dart // x ∈ l} := hnodup.getEquiv l
  have hpred : (fun x : N.Dart => x ∈ l) = (fun x : N.Dart => N.faceOf x = g) := by
    funext x
    exact propext (hmem x)
  have e₂ : {x : N.Dart // x ∈ l} ≃ {x : N.Dart // N.faceOf x = g} :=
    Equiv.subtypeEquivProp hpred
  change l.length = Nat.card {x : N.Dart // N.faceOf x = g}
  rw [← Nat.card_fin l.length]
  exact Nat.card_congr (e₁.trans e₂)

/-! ## The faces of the replacement, named -/

/-- The face of the replacement carrying an old face based outside the
region. -/
noncomputable def keptFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces) :
    (replaceGRegion M faces region).Face :=
  (replaceGRegionFaceEquiv M faces region).symm (Sum.inl ⟨f, hf⟩)

/-- The one face of the replacement bounded by the region's boundary cycle. -/
noncomputable def newFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) : (replaceGRegion M faces region).Face :=
  (replaceGRegionFaceEquiv M faces region).symm (Sum.inr PUnit.unit)

theorem keptFace_congr (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f g : M.Face) (hf : f ∉ faces)
    (hg : g ∉ faces) (h : f = g) :
    keptFace M faces region f hf = keptFace M faces region g hg := by
  subst h
  rfl

/-- A retained dart based outside the region lies on the kept face of its old
face. -/
theorem faceOf_eq_keptFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (d : KeptDart M faces)
    (hd : M.faceOf d.1 ∉ faces) :
    (replaceGRegion M faces region).faceOf d =
      keptFace M faces region (M.faceOf d.1) hd := by
  refine (Equiv.eq_symm_apply (replaceGRegionFaceEquiv M faces region)).2 ?_
  exact replaceGRegionFaceEquiv_faceOf_notMem M faces region d hd

/-- A retained dart based inside the region lies on the new face. -/
theorem faceOf_eq_newFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (d : KeptDart M faces)
    (hd : M.faceOf d.1 ∈ faces) :
    (replaceGRegion M faces region).faceOf d = newFace M faces region := by
  refine (Equiv.eq_symm_apply (replaceGRegionFaceEquiv M faces region)).2 ?_
  exact replaceGRegionFaceEquiv_faceOf_mem M faces region d hd

/-- A retained dart on a kept face has that face as its old face. -/
theorem faceOf_val_eq_of_eq_keptFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces)
    (d : KeptDart M faces)
    (hdf : (replaceGRegion M faces region).faceOf d =
      keptFace M faces region f hf) :
    M.faceOf d.1 = f := by
  have happly : replaceGRegionFaceEquiv M faces region
      ((replaceGRegion M faces region).faceOf d) = Sum.inl ⟨f, hf⟩ := by
    rw [hdf]
    exact (replaceGRegionFaceEquiv M faces region).apply_symm_apply
      (Sum.inl ⟨f, hf⟩)
  by_cases hd : M.faceOf d.1 ∈ faces
  · rw [replaceGRegionFaceEquiv_faceOf_mem M faces region d hd] at happly
    exact Sum.noConfusion happly
  · rw [replaceGRegionFaceEquiv_faceOf_notMem M faces region d hd] at happly
    have hinl := Sum.inl_injective happly
    exact congrArg (fun z : {g : M.Face // g ∉ faces} => z.1) hinl

/-- A retained dart on the new face is based inside the region. -/
theorem faceOf_val_mem_of_eq_newFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (d : KeptDart M faces)
    (hdf : (replaceGRegion M faces region).faceOf d = newFace M faces region) :
    M.faceOf d.1 ∈ faces := by
  by_cases hd : M.faceOf d.1 ∈ faces
  · exact hd
  · have happly : replaceGRegionFaceEquiv M faces region
        ((replaceGRegion M faces region).faceOf d) = Sum.inr PUnit.unit := by
      rw [hdf]
      exact (replaceGRegionFaceEquiv M faces region).apply_symm_apply
        (Sum.inr PUnit.unit)
    rw [replaceGRegionFaceEquiv_faceOf_notMem M faces region d hd] at happly
    exact Sum.noConfusion happly

/-! ## The ordered boundary of a kept face -/

theorem faceOf_notMem_of_mem_darts (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) (d : M.Dart)
    (hd : d ∈ B.darts) : M.faceOf d ∉ faces := by
  rw [(B.mem_iff d).1 hd]
  exact hf

/-- The retained darts of an ordered boundary of a face outside the region. -/
def keptFaceDarts (M : CombMap.{v}) (faces : Finset M.Face) (f : M.Face)
    (hf : f ∉ faces) (B : FaceBoundary M f) : List (KeptDart M faces) :=
  B.darts.pmap (keptDartOfNotMem M faces)
    (faceOf_notMem_of_mem_darts M faces f hf B)

theorem keptFaceDarts_ne_nil (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) :
    keptFaceDarts M faces f hf B ≠ [] :=
  (List.pmap_ne_nil_iff (keptDartOfNotMem M faces)
    (faceOf_notMem_of_mem_darts M faces f hf B)).2 B.nonempty

theorem keptFaceDarts_length (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) :
    (keptFaceDarts M faces f hf B).length = B.darts.length :=
  List.length_pmap

theorem keptFaceDarts_getElem_val (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) (i : ℕ)
    (hi : i < (keptFaceDarts M faces f hf B).length)
    (hj : i < B.darts.length) :
    ((keptFaceDarts M faces f hf B)[i]'hi).1 = B.darts[i]'hj :=
  congrArg (fun z : KeptDart M faces => z.1)
    (List.getElem_pmap (keptDartOfNotMem M faces)
      (faceOf_notMem_of_mem_darts M faces f hf B) hi)

theorem keptFaceDarts_head_val (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) :
    ((keptFaceDarts M faces f hf B).head
        (keptFaceDarts_ne_nil M faces f hf B)).1 =
      B.darts.head B.nonempty :=
  congrArg (fun z : KeptDart M faces => z.1)
    (List.head_pmap (faceOf_notMem_of_mem_darts M faces f hf B)
      (keptFaceDarts_ne_nil M faces f hf B))

theorem keptFaceDarts_getLast_val (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) :
    ((keptFaceDarts M faces f hf B).getLast
        (keptFaceDarts_ne_nil M faces f hf B)).1 =
      B.darts.getLast B.nonempty :=
  congrArg (fun z : KeptDart M faces => z.1)
    (List.getLast_pmap (faceOf_notMem_of_mem_darts M faces f hf B)
      (keptFaceDarts_ne_nil M faces f hf B))

theorem keptFaceDarts_nodup (M : CombMap.{v}) (faces : Finset M.Face)
    (f : M.Face) (hf : f ∉ faces) (B : FaceBoundary M f) :
    (keptFaceDarts M faces f hf B).Nodup := by
  refine List.Nodup.pmap ?_ B.nodup
  intro a ha b hb hab
  exact congrArg (fun z : KeptDart M faces => z.1) hab

theorem mem_keptFaceDarts_iff (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces)
    (B : FaceBoundary M f) (e : KeptDart M faces) :
    e ∈ keptFaceDarts M faces f hf B ↔
      (replaceGRegion M faces region).faceOf e =
        keptFace M faces region f hf := by
  constructor
  · intro hmem
    obtain ⟨a, ha, hae⟩ := List.mem_pmap.1 hmem
    have hfa : M.faceOf a = f := (B.mem_iff a).1 ha
    have hval : e.1 = a := by
      rw [← hae, keptDartOfNotMem_val]
    have hnot : M.faceOf e.1 ∉ faces := by
      rw [hval, hfa]
      exact hf
    rw [faceOf_eq_keptFace M faces region e hnot]
    apply keptFace_congr
    rw [hval]
    exact hfa
  · intro hface
    have hfa : M.faceOf e.1 = f :=
      faceOf_val_eq_of_eq_keptFace M faces region f hf e hface
    have hmemd : e.1 ∈ B.darts := (B.mem_iff e.1).2 hfa
    refine List.mem_pmap.2 ⟨e.1, hmemd, ?_⟩
    apply Subtype.ext
    rfl

theorem keptFaceDarts_chain (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces)
    (B : FaceBoundary M f) :
    (keptFaceDarts M faces f hf B).IsChain
      (fun x y => (replaceGRegion M faces region).facePerm x = y) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlen : (keptFaceDarts M faces f hf B).length = B.darts.length :=
    keptFaceDarts_length M faces f hf B
  have hi1 : i + 1 < B.darts.length := by
    rw [← hlen]
    exact hi
  have hi0 : i < B.darts.length := by omega
  have hivalid : i < (keptFaceDarts M faces f hf B).length := by omega
  have hvali : ((keptFaceDarts M faces f hf B)[i]'hivalid).1 = B.darts[i]'hi0 :=
    keptFaceDarts_getElem_val M faces f hf B i hivalid hi0
  have hvali1 : ((keptFaceDarts M faces f hf B)[i + 1]'hi).1 =
      B.darts[i + 1]'hi1 :=
    keptFaceDarts_getElem_val M faces f hf B (i + 1) hi hi1
  have hnot : M.faceOf ((keptFaceDarts M faces f hf B)[i]'hivalid).1 ∉ faces := by
    rw [hvali]
    exact faceOf_notMem_of_mem_darts M faces f hf B _ (List.getElem_mem hi0)
  apply Subtype.ext
  rw [replaceGRegion_facePerm_val_of_notMem M faces region _ hnot, hvali, hvali1]
  have hchain := B.chain
  rw [List.isChain_iff_getElem] at hchain
  exact hchain i hi1

theorem keptFaceDarts_closes (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces)
    (B : FaceBoundary M f) :
    (replaceGRegion M faces region).facePerm
        ((keptFaceDarts M faces f hf B).getLast
          (keptFaceDarts_ne_nil M faces f hf B)) =
      (keptFaceDarts M faces f hf B).head
        (keptFaceDarts_ne_nil M faces f hf B) := by
  have hlast := keptFaceDarts_getLast_val M faces f hf B
  have hhead := keptFaceDarts_head_val M faces f hf B
  have hnot : M.faceOf ((keptFaceDarts M faces f hf B).getLast
      (keptFaceDarts_ne_nil M faces f hf B)).1 ∉ faces := by
    rw [hlast]
    exact faceOf_notMem_of_mem_darts M faces f hf B _
      (List.getLast_mem B.nonempty)
  apply Subtype.ext
  rw [replaceGRegion_facePerm_val_of_notMem M faces region _ hnot, hlast, hhead]
  exact B.closes

/-- The ordered boundary of a kept face, given an ordered boundary of the old
face. -/
noncomputable def keptFaceBoundary (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (f : M.Face) (hf : f ∉ faces)
    (B : FaceBoundary M f) :
    FaceBoundary (replaceGRegion M faces region)
      (keptFace M faces region f hf) where
  darts := keptFaceDarts M faces f hf B
  nonempty := keptFaceDarts_ne_nil M faces f hf B
  nodup := keptFaceDarts_nodup M faces f hf B
  mem_iff := fun e => mem_keptFaceDarts_iff M faces region f hf B e
  chain := keptFaceDarts_chain M faces region f hf B
  closes := keptFaceDarts_closes M faces region f hf B
  length_eq_degree :=
    length_eq_faceDegree_of_nodup (replaceGRegion M faces region)
      (keptFace M faces region f hf) (keptFaceDarts M faces f hf B)
      (keptFaceDarts_nodup M faces f hf B)
      (fun e => mem_keptFaceDarts_iff M faces region f hf B e)

/-- Forgetting the retained-dart proofs returns the old ordered boundary, so a
kept face has the old face word. -/
theorem keptFaceBoundary_darts_map_val (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces) (f : M.Face)
    (hf : f ∉ faces) (B : FaceBoundary M f) :
    (keptFaceBoundary M faces region f hf B).darts.map Subtype.val =
      B.darts := by
  show (B.darts.pmap (keptDartOfNotMem M faces)
      (faceOf_notMem_of_mem_darts M faces f hf B)).map Subtype.val = B.darts
  rw [List.map_pmap, List.pmap_eq_self]
  intro a h
  rfl

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
