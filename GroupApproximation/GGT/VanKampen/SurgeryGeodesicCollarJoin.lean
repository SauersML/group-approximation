import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarAssembly
import GroupApproximation.GGT.VanKampen.SurgeryCornerJoinDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# The join stage of a collar insertion

A strip `p ++ q` along a side `p` of value one, with a nonempty rest `r`, is joined across.  The
corner join (`CornerJoin.Input.diagram`) of `alpha` of the last dart of `q` and `alpha` of the last
dart of `p` splits the strip face into a face enumerated by `q` and a face enumerated by `p`.  The
side `p` runs from the head of `p` to the head of `r`, and the join makes these one vertex, so `r`
is a simple closed walk of the join.  Replacing the strip face in the face set by the face of `q`
cuts the side off the face set, and the boundary darts become the darts of `r`
(`GeodesicCollar.joinStatement`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse

universe u w v

namespace GeodesicCollar

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Rotating a nonempty list past all but its last entry brings the last entry to the front. -/
theorem join_rotate_dropLast {α : Type*} {l : List α} (hl : l ≠ []) :
    l.rotate l.dropLast.length = l.getLast hl :: l.dropLast := by
  have h := List.rotate_append_length_eq l.dropLast [l.getLast hl]
  rw [List.dropLast_concat_getLast hl] at h
  exact h

namespace Strip

open scoped Classical

variable {Delta : DiscDiagram.{u, w, v} W} {S : Finset Delta.toCombMap.Face}
  {p r : List Delta.toCombMap.Dart} (X : Strip Delta S p r)

/-- The darts of the strip lie on the strip face. -/
theorem join_faceOf_eq_of_mem {e : Delta.toCombMap.Dart} (he : e ∈ p ++ X.q) :
    Delta.toCombMap.faceOf e = Delta.toCombMap.faceOf (p.head X.p_ne_nil) := by
  rw [(X.cycle.mem_iff e).mp he, List.head_append_of_ne_nil X.p_ne_nil]

/-- The darts on the strip face are the darts of the strip. -/
theorem join_mem_of_faceOf_eq {e : Delta.toCombMap.Dart}
    (he : Delta.toCombMap.faceOf e = Delta.toCombMap.faceOf (p.head X.p_ne_nil)) :
    e ∈ p ++ X.q := by
  refine (X.cycle.mem_iff e).mpr ?_
  rw [he, List.head_append_of_ne_nil X.p_ne_nil]

/-- The strip face reads a trivial word. -/
theorem join_cycle_value : RelLetter.listVal ((p ++ X.q).map Delta.label) = 1 := by
  have hF : RelLetter.listVal
      (Delta.faceWord (Delta.toCombMap.faceOf (p.head X.p_ne_nil))) = 1 := by
    rcases Delta.inner_face _ X.face_ne_outer with ⟨C, hC, hface⟩ | h
    · exact absurd hface (X.not_cell C hC)
    · exact h
  have hhead : Delta.toCombMap.faceOf ((p ++ X.q).head X.cycle.ne_nil) =
      Delta.toCombMap.faceOf (p.head X.p_ne_nil) := by
    rw [List.head_append_of_ne_nil X.p_ne_nil]
  obtain ⟨k, hk, hrot⟩ := (Delta.faceBoundary
      (Delta.toCombMap.faceOf (p.head X.p_ne_nil))).isFaceCycle.exists_rotate_eq X.cycle
    ((FaceBoundary.faceOf_head _).trans hhead.symm)
  rw [← hrot, List.map_rotate]
  exact PinchSplit.listVal_rotate_eq_one_of_eq_one k (by rw [List.length_map]; exact hk) hF

/-- The crossing darts `q` read a trivial word when the side does. -/
theorem join_q_value (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1) :
    RelLetter.listVal (X.q.map Delta.label) = 1 := by
  have h := X.join_cycle_value
  change ((p.map Delta.label).map RelLetter.val).prod = 1 at hval
  change (((p ++ X.q).map Delta.label).map RelLetter.val).prod = 1 at h
  change ((X.q.map Delta.label).map RelLetter.val).prod = 1
  rw [List.map_append, List.map_append, List.prod_append, hval, one_mul] at h
  exact h

/-- The crossing darts, from the last one, read a trivial word when the side does. -/
theorem join_left_value (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1) :
    RelLetter.listVal ((X.q.getLast X.q_ne_nil :: X.q.dropLast).map Delta.label) = 1 := by
  rw [← join_rotate_dropLast X.q_ne_nil, List.map_rotate]
  exact PinchSplit.listVal_rotate_eq_one_of_eq_one _
    (by rw [List.length_map, List.length_dropLast]; exact Nat.sub_le _ _) (X.join_q_value hval)

/-- The strip face turns from the last crossing dart to the head of the side. -/
theorem join_sigma_alpha_q :
    Delta.toCombMap.sigma (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil)) =
      p.head X.p_ne_nil := by
  have h := X.cycle.closes
  rw [List.getLast_append_of_ne_nil _ X.q_ne_nil, List.head_append_of_ne_nil X.p_ne_nil] at h
  exact h

/-- The last crossing dart ends at the head vertex of the side. -/
theorem join_vertexOf_alpha_q :
    Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil)) =
      Delta.toCombMap.vertexOf (p.head X.p_ne_nil) :=
  (Delta.toCombMap.vertexOf_eq_iff _ _).mpr (by
    rw [← X.join_sigma_alpha_q]
    exact Equiv.Perm.SameCycle.rfl.apply_right)

/-- The side ends at the head vertex of the rest. -/
theorem join_vertexOf_alpha_p (hr : r ≠ []) :
    Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (p.getLast X.p_ne_nil)) =
      Delta.toCombMap.vertexOf (r.head hr) :=
  (List.isChain_append.mp X.walk.chain).2.2 _ (List.getLast_mem_getLast? X.p_ne_nil) _
    (List.head_mem_head? hr)

/-- The rest ends at the head vertex of the side. -/
theorem join_vertexOf_alpha_r (hr : r ≠ []) :
    Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (r.getLast hr)) =
      Delta.toCombMap.vertexOf (p.head X.p_ne_nil) := by
  have h := X.walk.closes
  rw [List.getLast_append_of_ne_nil _ hr, List.head_append_of_ne_nil X.p_ne_nil] at h
  exact h

include X in
/-- The darts of the side and the darts of the rest start at distinct vertices. -/
theorem join_vertexOf_ne {d e : Delta.toCombMap.Dart} (hd : d ∈ p) (he : e ∈ r) :
    Delta.toCombMap.vertexOf d ≠ Delta.toCombMap.vertexOf e := by
  have h : (p.map Delta.toCombMap.vertexOf ++ r.map Delta.toCombMap.vertexOf).Nodup := by
    rw [← List.map_append]
    exact X.walk.vertex_nodup
  exact (List.nodup_append.mp h).2.2 _ (List.mem_map_of_mem hd) _ (List.mem_map_of_mem he)

/-- **The corner join across the strip**, of `alpha` of the last crossing dart and `alpha` of the
last dart of the side. -/
def joinInput (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1) (hr : r ≠ []) :
    CornerJoin.Input Delta where
  x := Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil)
  y := Delta.toCombMap.alpha (p.getLast X.p_ne_nil)
  not_same_vertex h := X.join_vertexOf_ne (List.head_mem X.p_ne_nil) (List.head_mem hr)
    (X.join_vertexOf_alpha_q.symm.trans
      (((Delta.toCombMap.vertexOf_eq_iff _ _).mpr h).trans (X.join_vertexOf_alpha_p hr)))
  xs := p.dropLast
  ys := X.q.dropLast
  cycle := by
    rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil),
      Delta.toCombMap.alpha_involutive (p.getLast X.p_ne_nil)]
    have hsplit : (p.dropLast ++ p.getLast X.p_ne_nil :: X.q.dropLast) ++
        [X.q.getLast X.q_ne_nil] = p ++ X.q := by
      rw [List.append_assoc, List.cons_append, List.dropLast_concat_getLast X.q_ne_nil,
        List.append_cons, List.dropLast_concat_getLast X.p_ne_nil]
    have h := X.cycle.rotate (p.dropLast ++ p.getLast X.p_ne_nil :: X.q.dropLast).length
    rw [← hsplit, List.rotate_append_length_eq] at h
    exact h
  face_ne_outer := by
    rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil),
      X.join_faceOf_eq_of_mem (List.mem_append_right p (List.getLast_mem X.q_ne_nil))]
    exact X.face_ne_outer
  not_cell := by
    rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil),
      X.join_faceOf_eq_of_mem (List.mem_append_right p (List.getLast_mem X.q_ne_nil))]
    exact X.not_cell
  left_value := by
    rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil)]
    exact X.join_left_value hval

/-- The joined face is the strip face. -/
theorem joinInput_face (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) :
    (X.joinInput hval hr).face = Delta.toCombMap.faceOf (p.head X.p_ne_nil) :=
  (congrArg Delta.toCombMap.faceOf (Delta.toCombMap.alpha_involutive _)).trans
    (X.join_faceOf_eq_of_mem (List.mem_append_right p (List.getLast_mem X.q_ne_nil)))

/-- The crossing darts enumerate the left new face. -/
theorem join_faceOf_q (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {e : Delta.toCombMap.Dart} (he : e ∈ X.q) :
    (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).faceOf e = (X.joinInput hval hr).leftFace := by
  refine ((X.joinInput hval hr).cycles.faceOf_left_iff e).mpr ?_
  by_cases hlast : e = X.q.getLast X.q_ne_nil
  · exact Or.inl (hlast.trans (Delta.toCombMap.alpha_involutive _).symm)
  · exact Or.inr (List.mem_dropLast_of_mem_of_ne_getLast he hlast)

/-- The side enumerates the right new face. -/
theorem join_faceOf_p (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {e : Delta.toCombMap.Dart} (he : e ∈ p) :
    (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).faceOf e = (X.joinInput hval hr).rightFace := by
  refine ((X.joinInput hval hr).cycles.faceOf_right_iff e).mpr ?_
  by_cases hlast : e = p.getLast X.p_ne_nil
  · exact Or.inl (hlast.trans (Delta.toCombMap.alpha_involutive _).symm)
  · exact Or.inr (List.mem_dropLast_of_mem_of_ne_getLast he hlast)

/-- **The face set after the join**: the left new face in place of the strip face. -/
noncomputable def joinFaces (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) :
    Finset (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).Face :=
  insert (X.joinInput hval hr).leftFace
    ((S.erase (X.joinInput hval hr).face).image (X.joinInput hval hr).kept)

/-- A face off the strip face is in the new face set exactly when it was in the face set. -/
theorem join_mem_kept (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {g : Delta.toCombMap.Face} (hg : g ≠ (X.joinInput hval hr).face) :
    (X.joinInput hval hr).kept g ∈ X.joinFaces hval hr ↔ g ∈ S := by
  rw [joinFaces, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨g', hg', heq⟩)
    · exact absurd h ((X.joinInput hval hr).kept_ne_left hg)
    · rw [Finset.mem_erase] at hg'
      rw [← (X.joinInput hval hr).kept_inj hg'.1 heq]
      exact hg'.2
  · intro h
    exact Or.inr ⟨g, Finset.mem_erase.mpr ⟨hg, h⟩, rfl⟩

theorem join_left_mem (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) : (X.joinInput hval hr).leftFace ∈ X.joinFaces hval hr :=
  Finset.mem_insert_self _ _

theorem join_right_not_mem (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) : (X.joinInput hval hr).rightFace ∉ X.joinFaces hval hr := by
  rw [joinFaces, Finset.mem_insert, Finset.mem_image]
  rintro (h | ⟨g, hg, heq⟩)
  · exact (X.joinInput hval hr).left_ne_right h.symm
  · exact (X.joinInput hval hr).kept_ne_right (Finset.mem_erase.mp hg).1 heq

/-- The new face set avoids the exterior. -/
theorem join_outer_not_mem (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) : (X.joinInput hval hr).diagram.outerFace ∉ X.joinFaces hval hr :=
  fun h => X.outerFace_not_mem
    ((X.join_mem_kept hval hr (X.joinInput hval hr).outer_ne_face).mp h)

/-- A dart off the strip face lies in the new face set exactly when it lay in the face set. -/
theorem join_mem_iff_of_ne (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {e : Delta.toCombMap.Dart}
    (he : Delta.toCombMap.faceOf e ≠ Delta.toCombMap.faceOf (p.head X.p_ne_nil)) :
    (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).faceOf e ∈ X.joinFaces hval hr ↔
      Delta.toCombMap.faceOf e ∈ S := by
  have he' : Delta.toCombMap.faceOf e ≠ (X.joinInput hval hr).face :=
    fun h => he (h.trans (X.joinInput_face hval hr))
  rw [← (X.joinInput hval hr).kept_faceOf e he']
  exact X.join_mem_kept hval hr he'

theorem join_mem_of_q (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {e : Delta.toCombMap.Dart} (he : e ∈ X.q) :
    (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).faceOf e ∈ X.joinFaces hval hr := by
  rw [X.join_faceOf_q hval hr he]
  exact X.join_left_mem hval hr

theorem join_not_mem_of_p (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) {e : Delta.toCombMap.Dart} (he : e ∈ p) :
    (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y).faceOf e ∉ X.joinFaces hval hr := by
  rw [X.join_faceOf_p hval hr he]
  exact X.join_right_not_mem hval hr

/-- **The join as a transport of the collar surgery.** -/
noncomputable def joinTransport (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) (D : RelGenSet G Lambda) (hlabel : ∀ d, D.IsLetter (Delta.label d)) :
    Transport D S (X.joinInput hval hr).diagram (X.joinFaces hval hr) where
  equiv := (X.joinInput hval hr).oEquivalent
  embedding := Function.Embedding.refl _
  label_isLetter := (X.joinInput hval hr).label_isLetter D hlabel
  alpha_embedding _ := rfl
  label_embedding _ := rfl
  outerDarts_eq := (X.joinInput hval hr).outerDarts_eq
  cellDarts_eq i _ := (X.joinInput hval hr).cellDarts_eq i
  cell_mem_iff i := by
    change (Embedded.cell (X.joinInput hval hr).diagram
      ((X.joinInput hval hr).cellMap.indexEquiv i)).face ∈ X.joinFaces hval hr ↔ _
    rw [(X.joinInput hval hr).cellMap.indexed_cell i]
    exact X.join_mem_kept hval hr
      ((X.joinInput hval hr).not_cell _ (Embedded.cell_mem Delta i))

theorem joinTransport_map (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1)
    (hr : r ≠ []) (D : RelGenSet G Lambda) (hlabel : ∀ d, D.IsLetter (Delta.label d)) :
    r.map (X.joinTransport hval hr D hlabel).embedding = r :=
  List.map_id r

/-- **The rest is a simple closed walk of the join**, since the join makes the end vertices of the
side one vertex. -/
theorem join_walk (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1) (hr : r ≠ []) :
    IsSimpleClosedWalk (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y) r := by
  have hnd : (p.map Delta.toCombMap.vertexOf ++ r.map Delta.toCombMap.vertexOf).Nodup := by
    rw [← List.map_append]
    exact X.walk.vertex_nodup
  have hrnd : (r.map Delta.toCombMap.vertexOf).Nodup := (List.nodup_append.mp hnd).2.1
  have hiff := CornerJoin.vertexOf_eq_iff Delta.toCombMap (X.joinInput hval hr).x
    (X.joinInput hval hr).y (X.joinInput hval hr).not_same_vertex
  refine
    { ne_nil := hr
      chain := X.walk.chain.right_of_append.imp_of_mem_imp fun _ _ _ _ h =>
        (hiff _ _).mpr (Or.inl h)
      closes := (hiff _ _).mpr (Or.inr ⟨Or.inl (X.join_vertexOf_alpha_q.trans
        (X.join_vertexOf_alpha_r hr).symm), Or.inr (X.join_vertexOf_alpha_p hr)⟩)
      vertex_nodup := (List.Nodup.of_map Delta.toCombMap.vertexOf hrnd).map_on ?_
      alpha_not_mem := fun d hd h =>
        X.walk.alpha_not_mem d (List.mem_append_right p hd) (List.mem_append_right p h) }
  intro d hd e he h
  rcases (hiff d e).mp h with h | ⟨hd' | hd', he' | he'⟩
  · exact List.inj_on_of_nodup_map hrnd hd he h
  · exact absurd (X.join_vertexOf_alpha_q.symm.trans hd')
      (X.join_vertexOf_ne (List.head_mem X.p_ne_nil) hd)
  · exact absurd (X.join_vertexOf_alpha_q.symm.trans hd')
      (X.join_vertexOf_ne (List.head_mem X.p_ne_nil) hd)
  · exact absurd (X.join_vertexOf_alpha_q.symm.trans he')
      (X.join_vertexOf_ne (List.head_mem X.p_ne_nil) he)
  · exact List.inj_on_of_nodup_map hrnd hd he (hd'.symm.trans he')

/-- **The boundary darts of the new face set are the darts of the rest.** -/
theorem join_boundary (hval : RelLetter.listVal (Embedded.dartWord Delta p) = 1) (hr : r ≠ [])
    (d : Delta.toCombMap.Dart) :
    IsBoundaryDart (CornerJoin.toCombMap Delta.toCombMap (X.joinInput hval hr).x
      (X.joinInput hval hr).y) (X.joinFaces hval hr) d ↔ d ∈ r := by
  have hF := X.face_mem
  constructor
  · rintro ⟨hd, hαd⟩
    by_cases hαF : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) =
        Delta.toCombMap.faceOf (p.head X.p_ne_nil)
    · exfalso
      rcases List.mem_append.mp (X.join_mem_of_faceOf_eq hαF) with hαp | hαq
      · apply ((X.boundary _).mpr (List.mem_append_left r hαp)).2
        rw [Delta.toCombMap.alpha_involutive d]
        by_cases hdF : Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf (p.head X.p_ne_nil)
        · rw [hdF]
          exact hF
        · exact (X.join_mem_iff_of_ne hval hr hdF).mp hd
      · exact hαd (X.join_mem_of_q hval hr hαq)
    · have hαS : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ S :=
        fun h => hαd ((X.join_mem_iff_of_ne hval hr hαF).mpr h)
      by_cases hdF : Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf (p.head X.p_ne_nil)
      · exfalso
        rcases List.mem_append.mp (X.join_mem_of_faceOf_eq hdF) with hdp | hdq
        · exact X.join_not_mem_of_p hval hr hdp hd
        · exact hαS (X.alpha_mem d hdq)
      · rcases List.mem_append.mp
            ((X.boundary d).mp (And.intro ((X.join_mem_iff_of_ne hval hr hdF).mp hd) hαS)) with
          hdp | hdr
        · exact absurd (X.join_faceOf_eq_of_mem (List.mem_append_left X.q hdp)) hdF
        · exact hdr
  · intro hdr
    have hb := (X.boundary d).mpr (List.mem_append_right p hdr)
    have hαF : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠
        Delta.toCombMap.faceOf (p.head X.p_ne_nil) := fun h => hb.2 (by rw [h]; exact hF)
    refine And.intro ?_ (fun h => hb.2 ((X.join_mem_iff_of_ne hval hr hαF).mp h))
    by_cases hdF : Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf (p.head X.p_ne_nil)
    · rcases List.mem_append.mp (X.join_mem_of_faceOf_eq hdF) with hdp | hdq
      · exact absurd rfl (X.join_vertexOf_ne hdp hdr)
      · exact X.join_mem_of_q hval hr hdq
    · exact (X.join_mem_iff_of_ne hval hr hdF).mpr hb.1

end Strip

open scoped Classical in
/-- **Stage 3, the join**: a strip whose side has value one, with a nonempty rest, gives a collar
walk reading the empty word. -/
theorem joinStatement : JoinStatement.{u, w, v} := by
  intro G _ Lambda W D Delta hlabel S p r X hr hval
  refine ⟨(X.joinInput hval hr).diagram, X.joinFaces hval hr, X.joinTransport hval hr D hlabel,
    [], X.join_outer_not_mem hval hr, ?_, ?_, rfl⟩
  · rw [List.nil_append, X.joinTransport_map hval hr D hlabel]
    exact X.join_walk hval hr
  · intro d
    rw [List.nil_append, X.joinTransport_map hval hr D hlabel]
    exact X.join_boundary hval hr d

end GeodesicCollar

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.join_rotate_dropLast
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_cycle_value
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_left_value
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_vertexOf_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.joinInput_face
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_mem_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_mem_iff_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.Strip.join_boundary
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.joinStatement
