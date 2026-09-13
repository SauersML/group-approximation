import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarJoin
import GroupApproximation.GGT.VanKampen.GFaceSplitCorners
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CornerInsertion
import GroupApproximation.Meta.AxiomGuard

/-!
# The insertion stage of a collar

A strip `p ++ q` along a side `p`, with rest `r`, receives a nonempty word `g` of the value of `p`.
The word goes across the strip face from the corner before `p` to the corner after `p`
(`GFaceWordInsertion.exists_split_corner_output`).  This splits the strip face into a prefix side,
enumerated by the reversed path and `p`, and a suffix side, enumerated by the path and `q`.
Replacing the strip face in the face set by the suffix side cuts `p` off the face set, and the
boundary darts become the inserted path followed by the darts of `r`
(`GeodesicCollar.insertStatement`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse

universe u w v

namespace GeodesicCollar

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Strip

open scoped Classical

variable {Delta : DiscDiagram.{u, w, v} W} {S : Finset Delta.toCombMap.Face}
  {p r : List Delta.toCombMap.Dart} (X : Strip Delta S p r)

/-- The crossing darts start where the side ends. -/
theorem insert_vertexOf_q_head :
    Delta.toCombMap.vertexOf (X.q.head X.q_ne_nil) =
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (p.getLast X.p_ne_nil)) := by
  have h : Delta.toCombMap.sigma (Delta.toCombMap.alpha (p.getLast X.p_ne_nil)) =
      X.q.head X.q_ne_nil :=
    (List.isChain_append.mp X.cycle.chain).2.2 _ (List.getLast_mem_getLast? X.p_ne_nil) _
      (List.head_mem_head? X.q_ne_nil)
  rw [← h]
  exact Delta.toCombMap.vertexOf_sigma _

/-- A rotation of a traversal onto the strip starts at the head of the side. -/
theorem insert_start_dart {f : Delta.toCombMap.Face} (B : FaceBoundary Delta.toCombMap f)
    {start : Fin B.darts.length} (hrot : B.darts.rotate start.val = p ++ X.q) :
    B.darts.get start = p.head X.p_ne_nil := by
  have h := FaceBoundary.rotate_head B start
  simp only [FaceBoundary.rotate, hrot, List.head_append_of_ne_nil X.p_ne_nil] at h
  exact h.symm

/-- Advancing a rotation onto the strip by the length of the side reaches the head of `q`. -/
theorem insert_finish_dart {f : Delta.toCombMap.Face} (B : FaceBoundary Delta.toCombMap f)
    {start finish : Fin B.darts.length} (hrot : B.darts.rotate start.val = p ++ X.q)
    (hoff : B.forwardOffset start finish = p.length) :
    B.darts.get finish = X.q.head X.q_ne_nil := by
  have hfin : B.darts.rotate finish.val = X.q ++ p := by
    rw [← B.forwardOffset_add_mod start finish, hoff, List.rotate_mod, Nat.add_comm p.length,
      ← List.rotate_rotate, hrot, List.rotate_append_length_eq]
  have h := FaceBoundary.rotate_head B finish
  simp only [FaceBoundary.rotate, hfin, List.head_append_of_ne_nil X.q_ne_nil] at h
  exact h.symm

/-- The darts of the rest are not on the strip face. -/
theorem insert_faceOf_ne_of_mem_r {d : Delta.toCombMap.Dart} (hd : d ∈ r) :
    Delta.toCombMap.faceOf d ≠ Delta.toCombMap.faceOf (p.head X.p_ne_nil) := by
  intro h
  rcases List.mem_append.mp (X.join_mem_of_faceOf_eq h) with hdp | hdq
  · exact X.join_vertexOf_ne hdp hd rfl
  · exact ((X.boundary d).mpr (List.mem_append_right p hd)).2 (X.alpha_mem d hdq)

/-- The darts of the rest do not cross to the strip face. -/
theorem insert_faceOf_alpha_ne_of_mem_r {d : Delta.toCombMap.Dart} (hd : d ∈ r) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠
      Delta.toCombMap.faceOf (p.head X.p_ne_nil) := by
  intro h
  refine ((X.boundary d).mpr (List.mem_append_right p hd)).2 ?_
  rw [h]
  exact X.face_mem

section Insert

variable {D : RelGenSet G Lambda}
  {start finish :
    Fin (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.length}
  {g : List (RelLetter G Lambda)}
  (R : GFaceWordInsertion.SplitCornerOutput D Delta (Delta.toCombMap.faceOf (p.head X.p_ne_nil))
    X.face_ne_outer X.not_cell start finish g)

/-- A dart off the strip face lies on the retained copy of its face. -/
theorem insert_faceOf_kept {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ≠ Delta.toCombMap.faceOf (p.head X.p_ne_nil)) :
    R.diagram.toCombMap.faceOf
        ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts d) =
      (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).faces
        (Delta.toCombMap.faceOf d) := by
  apply ((R.diagram.faceBoundary
    ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).faces
      (Delta.toCombMap.faceOf d))).mem_iff
    ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts d)).mp
  rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).face_boundary _ hd]
  exact List.mem_map.mpr ⟨d, ((Delta.faceBoundary _).mem_iff d).mpr rfl, rfl⟩

/-- The crossing darts lie on the suffix side. -/
theorem insert_faceOf_q
    (hdrop : ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val).drop ((Delta.faceBoundary
        (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish) = X.q)
    {d : Delta.toCombMap.Dart} (hd : d ∈ X.q) :
    R.diagram.toCombMap.faceOf
        ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts d) =
      R.suffixSide := by
  refine ((R.diagram.faceBoundary R.suffixSide).mem_iff _).mp ?_
  rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop]
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨d, hd, rfl⟩))

/-- The darts on the suffix side are the inserted path and the crossing darts. -/
theorem insert_mem_of_suffixSide
    (hdrop : ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val).drop ((Delta.faceBoundary
        (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish) = X.q)
    {x : R.diagram.toCombMap.Dart} (hx : R.diagram.toCombMap.faceOf x = R.suffixSide) :
    x ∈ R.darts ++
      X.q.map (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts := by
  have h := ((R.diagram.faceBoundary R.suffixSide).mem_iff x).mpr hx
  rw [GFaceWordInsertion.SplitCornerOutput.suffixSide_darts_original R, hdrop] at h
  exact h

/-- The face set of the insertion: the suffix side in place of the strip face. -/
noncomputable def insertFaces : Finset R.diagram.toCombMap.Face :=
  insert R.suffixSide ((S.erase (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).map
    (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).faces)

theorem insert_suffixSide_mem : R.suffixSide ∈ X.insertFaces R :=
  Finset.mem_insert_self _ _

/-- A retained face off the strip face lies in the new face set exactly when it lay in the old. -/
theorem insert_mem_kept {c : Delta.toCombMap.Face}
    (hc : c ≠ Delta.toCombMap.faceOf (p.head X.p_ne_nil)) :
    (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).faces c ∈
      X.insertFaces R ↔ c ∈ S := by
  rw [insertFaces, Finset.mem_insert, Finset.mem_map', Finset.mem_erase]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (R.suffixSide_not_kept c hc)
    · exact h
  · exact fun h => Or.inr ⟨hc, h⟩

theorem insert_prefixSide_not_mem : R.prefixSide ∉ X.insertFaces R := by
  rw [insertFaces, Finset.mem_insert, Finset.mem_map]
  rintro (h | ⟨c, hc, h⟩)
  · exact R.prefixSide_ne_suffixSide h
  · exact R.prefixSide_not_kept c (Finset.ne_of_mem_erase hc) h

theorem insert_outerFace_not_mem : R.diagram.outerFace ∉ X.insertFaces R := by
  rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).outer,
    X.insert_mem_kept R X.face_ne_outer.symm]
  exact X.outerFace_not_mem

/-- **The insertion as a transport of the collar surgery.** -/
noncomputable def insertTransport : Transport D S R.diagram (X.insertFaces R) where
  equiv := (GFaceWordInsertion.CornerOutput.originalReplacement R.toCellOutput).oEquivalent
  embedding := (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts
  label_isLetter := R.label_admissible
  alpha_embedding := (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha
  label_embedding := (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).label
  outerDarts_eq := by
    change Embedded.invDarts R.diagram (R.diagram.faceBoundary R.diagram.outerFace).darts =
      (Embedded.invDarts Delta (Delta.faceBoundary Delta.outerFace).darts).map
        (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts
    rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).outer,
      (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).face_boundary _
        X.face_ne_outer.symm,
      (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).invDarts_map]
  cellDarts_eq i _ := by
    change (R.diagram.faceBoundary (Embedded.cell R.diagram
      ((GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).indexEquiv i)).face).darts =
        _
    rw [(GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).indexed_cell i,
      (GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).face_eq]
    exact (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).face_boundary _
      (X.not_cell _ (Embedded.cell_mem Delta i))
  cell_mem_iff i := by
    change (Embedded.cell R.diagram
      ((GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).indexEquiv i)).face ∈
        X.insertFaces R ↔ _
    rw [(GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).indexed_cell i,
      (GFaceWordInsertion.CornerOutput.originalCellMap R.toCellOutput).face_eq]
    exact X.insert_mem_kept R (X.not_cell _ (Embedded.cell_mem Delta i))

/-- **The inserted path followed by the rest is a simple closed walk.** -/
theorem insert_walk
    (hstart : (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.get start =
      p.head X.p_ne_nil)
    (hfinish : (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.get finish =
      X.q.head X.q_ne_nil) :
    IsSimpleClosedWalk R.diagram.toCombMap
      (R.darts ++
        r.map (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts) := by
  have hvd : ∀ d, R.diagram.toCombMap.vertexOf
      ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts d) =
        R.vertices (Delta.toCombMap.vertexOf d) := R.vertex_darts
  have hinit : R.diagram.toCombMap.vertexOf (R.darts.head R.nonempty) =
      R.vertices (Delta.toCombMap.vertexOf (p.head X.p_ne_nil)) :=
    (GFaceWordInsertion.CornerOutput.initial_original R.toCellOutput).trans
      (congrArg (fun d => R.vertices (Delta.toCombMap.vertexOf d)) hstart)
  have hterm : R.diagram.toCombMap.vertexOf
      (R.diagram.toCombMap.alpha (R.darts.getLast R.nonempty)) =
        R.vertices (Delta.toCombMap.vertexOf (X.q.head X.q_ne_nil)) :=
    (GFaceWordInsertion.CornerOutput.terminal_original R.toCellOutput).trans
      (congrArg (fun d => R.vertices (Delta.toCombMap.vertexOf d)) hfinish)
  have hget0 : ∀ i : Fin R.darts.length, ¬0 < i.val → R.darts.get i = R.darts.head R.nonempty := by
    intro i hi
    simp only [List.get_eq_getElem, List.head_eq_getElem, (by omega : i.val = 0)]
  have hnd : (p.map Delta.toCombMap.vertexOf ++ r.map Delta.toCombMap.vertexOf).Nodup := by
    rw [← List.map_append]
    exact X.walk.vertex_nodup
  have hmap : ∀ d e : Delta.toCombMap.Dart,
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e →
        R.diagram.toCombMap.vertexOf (R.diagram.toCombMap.alpha
          ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts d)) =
          R.diagram.toCombMap.vertexOf
            ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts e) := by
    intro d e h
    rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha, hvd, hvd, h]
  refine ⟨List.append_ne_nil_of_left_ne_nil R.nonempty _, ?_, ?_, ?_, ?_⟩
  · refine List.isChain_append.mpr ⟨R.chain, List.isChain_map_of_isChain
      (S := fun d e => R.diagram.toCombMap.vertexOf (R.diagram.toCombMap.alpha d) =
        R.diagram.toCombMap.vertexOf e) _ hmap X.walk.chain.right_of_append, ?_⟩
    intro x hx y hy
    rw [Option.mem_def, List.head?_map, Option.map_eq_some_iff] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    have hr : r ≠ [] := by
      intro hnil
      rw [hnil, List.head?_nil] at hd
      cases hd
    rw [List.head?_eq_some_head hr, Option.some_inj] at hd
    subst hd
    rw [Option.mem_def, List.getLast?_eq_some_getLast R.nonempty, Option.some_inj] at hx
    subst hx
    show R.diagram.toCombMap.vertexOf (R.diagram.toCombMap.alpha (R.darts.getLast R.nonempty)) =
      R.diagram.toCombMap.vertexOf
        ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts (r.head hr))
    rw [hterm, hvd, X.insert_vertexOf_q_head, X.join_vertexOf_alpha_p hr]
  · rw [List.head_append_of_ne_nil R.nonempty, hinit]
    by_cases hr : r = []
    · have h := X.walk.closes
      simp only [hr, List.append_nil] at h
      simp only [hr, List.map_nil, List.append_nil]
      rw [hterm, X.insert_vertexOf_q_head, h]
    · have hne : r.map (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts ≠
          [] := fun h => hr (List.map_eq_nil_iff.mp h)
      rw [List.getLast_append_of_ne_nil _ hne, List.getLast_map,
        (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha, hvd,
        X.join_vertexOf_alpha_r hr]
  · rw [List.map_append, List.nodup_append]
    refine ⟨R.nodup.map_on fun x hx y hy hxy => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hx
      obtain ⟨j, rfl⟩ := List.get_of_mem hy
      by_cases hi : 0 < i.val
      · by_cases hj : 0 < j.val
        · rw [(R.internal_vertex_eq_iff i j hi hj).mp hxy]
        · exact (R.internal_fresh i hi (by rw [hxy, hget0 j hj, hinit]; exact ⟨_, rfl⟩)).elim
      · by_cases hj : 0 < j.val
        · exact (R.internal_fresh j hj (by rw [← hxy, hget0 i hi, hinit]; exact ⟨_, rfl⟩)).elim
        · rw [hget0 i hi, hget0 j hj]
    · have h : (r.map (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts).map
          R.diagram.toCombMap.vertexOf = (r.map Delta.toCombMap.vertexOf).map R.vertices := by
        refine List.map_map.trans ?_
        refine Eq.trans ?_ List.map_map.symm
        exact List.map_congr_left fun d _ => hvd d
      rw [h]
      exact (List.nodup_append.mp hnd).2.1.map R.vertices.injective
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      obtain ⟨i, rfl⟩ := List.get_of_mem hx
      rw [hvd] at hab
      by_cases hi : 0 < i.val
      · exact R.internal_fresh i hi (by rw [hab]; exact ⟨_, rfl⟩)
      · rw [hget0 i hi, hinit] at hab
        exact X.join_vertexOf_ne (List.head_mem X.p_ne_nil) hd (R.vertices.injective hab)
  · intro x hx hαx
    rcases List.mem_append.mp hx with hxc | hxr
    · rcases List.mem_append.mp hαx with hαc | hαr
      · exact R.prefixSide_ne_suffixSide
          ((GFaceWordInsertion.SplitOutput.faceOf_of_mem_invDarts R
            ((Embedded.mem_invDarts_iff R.darts x).mpr hαc)).symm.trans
          (GFaceWordInsertion.SplitOutput.faceOf_of_mem_darts R hxc))
      · obtain ⟨d, -, hdx⟩ := List.mem_map.mp hαr
        refine R.path_disjoint x hxc ⟨Delta.toCombMap.alpha d, ?_⟩
        show (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts
          (Delta.toCombMap.alpha d) = x
        rw [← (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha, hdx,
          R.diagram.toCombMap.alpha_involutive x]
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hxr
      rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha] at hαx
      rcases List.mem_append.mp hαx with hαc | hαr
      · exact R.path_disjoint _ hαc ⟨Delta.toCombMap.alpha d, rfl⟩
      · obtain ⟨e, he, hed⟩ := List.mem_map.mp hαr
        obtain rfl :=
          (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts.injective hed
        exact X.walk.alpha_not_mem d (List.mem_append_right p hd) (List.mem_append_right p he)

/-- **The boundary of the new face set is the inserted path followed by the rest.** -/
theorem insert_boundary
    (hdrop : ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val).drop ((Delta.faceBoundary
        (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish) = X.q)
    (x : R.diagram.toCombMap.Dart) :
    IsBoundaryDart R.diagram.toCombMap (X.insertFaces R) x ↔
      x ∈ R.darts ++
        r.map (GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).darts := by
  constructor
  · rintro ⟨hx, hαx⟩
    rw [insertFaces, Finset.mem_insert] at hx
    rcases hx with hxs | hxk
    · rcases List.mem_append.mp (X.insert_mem_of_suffixSide R hdrop hxs) with hxc | hxq
      · exact List.mem_append_left _ hxc
      · exfalso
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hxq
        refine hαx ?_
        rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha]
        by_cases hαF : Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) =
          Delta.toCombMap.faceOf (p.head X.p_ne_nil)
        · rcases List.mem_append.mp (X.join_mem_of_faceOf_eq hαF) with hαp | hαq
          · exfalso
            refine ((X.boundary _).mpr (List.mem_append_left r hαp)).2 ?_
            rw [Delta.toCombMap.alpha_involutive e,
              X.join_faceOf_eq_of_mem (List.mem_append_right p he)]
            exact X.face_mem
          · rw [X.insert_faceOf_q R hdrop hαq]
            exact X.insert_suffixSide_mem R
        · rw [X.insert_faceOf_kept R hαF, X.insert_mem_kept R hαF]
          exact X.alpha_mem e he
    · obtain ⟨d, rfl, hdS⟩ :=
        ((GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).faceOf_mem_iff
          (S.erase (Delta.toCombMap.faceOf (p.head X.p_ne_nil)))
          (Finset.notMem_erase _ S) x).mp hxk
      obtain ⟨hdF, hdS⟩ := Finset.mem_erase.mp hdS
      rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha] at hαx
      have hαS : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ S := by
        intro hαS
        by_cases hαF : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) =
          Delta.toCombMap.faceOf (p.head X.p_ne_nil)
        · rcases List.mem_append.mp (X.join_mem_of_faceOf_eq hαF) with hαp | hαq
          · refine ((X.boundary _).mpr (List.mem_append_left r hαp)).2 ?_
            rw [Delta.toCombMap.alpha_involutive d]
            exact hdS
          · exact hαx (by rw [X.insert_faceOf_q R hdrop hαq]; exact X.insert_suffixSide_mem R)
        · exact hαx (by rw [X.insert_faceOf_kept R hαF, X.insert_mem_kept R hαF]; exact hαS)
      rcases List.mem_append.mp ((X.boundary d).mp (show _ ∧ _ from ⟨hdS, hαS⟩)) with hdp | hdr
      · exact absurd (X.join_faceOf_eq_of_mem (List.mem_append_left X.q hdp)) hdF
      · exact List.mem_append_right _ (List.mem_map_of_mem hdr)
  · intro hx
    show _ ∧ _
    rcases List.mem_append.mp hx with hxc | hxr
    · refine ⟨?_, ?_⟩
      · rw [GFaceWordInsertion.SplitOutput.faceOf_of_mem_darts R hxc]
        exact X.insert_suffixSide_mem R
      · have hαc : R.diagram.toCombMap.alpha x ∈ Embedded.invDarts R.diagram R.darts :=
          (Embedded.mem_invDarts_iff R.darts (R.diagram.toCombMap.alpha x)).mpr
            (by rw [R.diagram.toCombMap.alpha_involutive x]; exact hxc)
        rw [GFaceWordInsertion.SplitOutput.faceOf_of_mem_invDarts R hαc]
        exact X.insert_prefixSide_not_mem R
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hxr
      have hbd := (X.boundary d).mpr (List.mem_append_right p hd)
      refine ⟨?_, ?_⟩
      · rw [X.insert_faceOf_kept R (X.insert_faceOf_ne_of_mem_r hd),
          X.insert_mem_kept R (X.insert_faceOf_ne_of_mem_r hd)]
        exact hbd.1
      · rw [(GFaceWordInsertion.CornerOutput.originalEmbedding R.toCellOutput).alpha,
          X.insert_faceOf_kept R (X.insert_faceOf_alpha_ne_of_mem_r hd),
          X.insert_mem_kept R (X.insert_faceOf_alpha_ne_of_mem_r hd)]
        exact hbd.2

end Insert

end Strip

/-- **The insertion stage.**  A nonempty word of letters with the value of the side of a strip,
inserted across the strip face from the corner before the side to the corner after it, gives a
collar walk reading that word. -/
theorem insertStatement : InsertStatement.{u, w, v} := by
  intro G _ Lambda W D hsymm Delta hlabel S p r X g hne hword hval
  have hq := List.length_pos_iff.mpr X.q_ne_nil
  have hhead : Delta.toCombMap.faceOf
      ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.head
        (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).nonempty) =
      Delta.toCombMap.faceOf ((p ++ X.q).head X.cycle.ne_nil) := by
    rw [FaceBoundary.faceOf_head, List.head_append_of_ne_nil X.p_ne_nil]
  obtain ⟨k, -, hrot0⟩ :=
    (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).isFaceCycle.exists_rotate_eq
      X.cycle hhead
  have hlen : (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.length =
      p.length + X.q.length := by
    rw [← List.length_rotate
      (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts k, hrot0,
      List.length_append]
  obtain ⟨start, hstart⟩ : ∃ start :
      Fin (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.length,
      start.val =
        k % (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.length :=
    ⟨⟨_, Nat.mod_lt k (by omega)⟩, rfl⟩
  have hrot : (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val = p ++ X.q := by
    rw [hstart, List.rotate_mod, hrot0]
  obtain ⟨finish, hoff⟩ := CornerInsertion.exists_forwardOffset_eq
    (Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))) start (k := p.length)
    (by omega)
  have htake : ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val).take ((Delta.faceBoundary
        (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish) = p := by
    rw [hrot, hoff]
    exact List.take_left' rfl
  have hdrop : ((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
      start.val).drop ((Delta.faceBoundary
        (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish) = X.q := by
    rw [hrot, hoff]
    exact List.drop_left' rfl
  have hvalue : RelLetter.listVal g = RelLetter.listVal
      ((((Delta.faceBoundary (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).darts.rotate
        start.val).take ((Delta.faceBoundary
          (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).forwardOffset start finish)).map
            Delta.label) := by
    rw [htake]
    exact hval
  obtain ⟨R⟩ := GFaceWordInsertion.exists_split_corner_output D Delta hlabel _ X.face_ne_outer
    X.not_cell start finish g hne hword
    (fun l hl => by
      cases l with
      | base x => exact hsymm x (hword _ hl)
      | comp lam h => exact inv_mem (hword _ hl))
    hvalue
  exact ⟨R.diagram, X.insertFaces R, X.insertTransport R, R.darts, X.insert_outerFace_not_mem R,
    X.insert_walk R (X.insert_start_dart _ hrot) (X.insert_finish_dart _ hrot hoff),
    X.insert_boundary R hdrop, R.word_eq⟩

end GeodesicCollar

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_vertexOf_q_head
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_start_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_finish_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_faceOf_ne_of_mem_r
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_faceOf_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_mem_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.insert_boundary
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.insertStatement

