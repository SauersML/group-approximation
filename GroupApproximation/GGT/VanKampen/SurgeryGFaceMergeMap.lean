import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.GGT.VanKampen.EdgeDeletionFaces
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionConnected
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces of a map after deleting an edge between two faces

The map layer of the G-face merge surgery (`SurgeryGFaceMerge`).  Let `a` be a dart whose
two sides lie on distinct faces `F₁ = faceOf a` and `F₂ = faceOf (alpha a)`, and let
`C : EdgeDeletion.MergeCycles M a` enumerate them from the edge as `a :: xs` and
`alpha a :: ys`.  Deleting the edge of `a` gives `EdgeDeletion.toCombMap M a`, and this file
names its faces and allocates a traversal of each of them.

* `MergeCycles.append_ne_nil`: in a connected map where some dart survives, the merged
  enumeration `xs ++ ys` is nonempty.
* `MergeCycles.mergedFace`: the face of the lift of `xs ++ ys`
  (`faceOf_eq_mergedFace_iff`: a surviving dart lies on it exactly when its old face is `F₁`
  or `F₂`).
* `keptFace M a FB g hg`: for an old face `g` off `F₁` and `F₂`, the face of the lift of its
  old traversal `FB g` (`faceOf_eq_keptFace_iff`: a surviving dart lies on it exactly when
  its old face is `g`).  It is injective (`keptFace_inj`) and never the merged face
  (`MergeCycles.keptFace_ne_mergedFace`).
* `MergeCycles.face_cases`: every face of the deleted map is the merged face or a kept face.
* `MergeCycles.faceBoundary`: a traversal of every face; the merged face reads the lift of
  `xs ++ ys` (`faceBoundary_mergedFace_map_value`) and a kept face reads the lift of the old
  traversal (`faceBoundary_keptFace_map_value`).
* `MergeCycles.faceCount_add_one`: exactly one face disappears.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv

universe u

/-- Transporting a face boundary along an equality of faces keeps its darts. -/
theorem FaceBoundary.darts_mpr {M : CombMap.{u}} {f g : M.Face} (h : f = g)
    (B : FaceBoundary M g) : ((congrArg (FaceBoundary M) h).mpr B).darts = B.darts := by
  subst h
  rfl

namespace EdgeDeletion

/-- **Every dart heads a face cycle**, written with the dart as the head. -/
theorem exists_isFaceCycle_cons (M : CombMap.{u}) (d : M.Dart) :
    ∃ rest : List M.Dart, M.IsFaceCycle (d :: rest) := by
  obtain ⟨l, hl, hhead⟩ := M.exists_isFaceCycle_head d
  cases l with
  | nil => exact absurd rfl hl.ne_nil
  | cons x rest =>
      have hx : x = d := hhead
      subst hx
      exact ⟨rest, hl⟩

/-- **The two sides of an edge on distinct faces**, enumerated from the edge. -/
noncomputable def mergeCyclesOf (M : CombMap.{u}) (a : M.Dart)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) : MergeCycles M a where
  xs := Classical.choose (exists_isFaceCycle_cons M a)
  ys := Classical.choose (exists_isFaceCycle_cons M (M.alpha a))
  cycO := Classical.choose_spec (exists_isFaceCycle_cons M a)
  cycG := Classical.choose_spec (exists_isFaceCycle_cons M (M.alpha a))
  face_ne := hface

/-- A dart on a face off both sides of the deleted edge, together with its successor, avoids
the deleted edge. -/
theorem avoid_of_off {M : CombMap.{u}} {a : M.Dart} {g : M.Face}
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) {d : M.Dart} (hd : M.faceOf d = g) :
    d ≠ a ∧ d ≠ M.alpha a ∧ M.facePerm d ≠ a ∧ M.facePerm d ≠ M.alpha a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hg.1 hd.symm
  · rintro rfl
    exact hg.2 hd.symm
  · intro h
    apply hg.1
    rw [← hd, ← M.faceOf_facePerm d, h]
  · intro h
    apply hg.2
    rw [← hd, ← M.faceOf_facePerm d, h]

/-- **A face cycle avoiding the deleted edge lifts** to a face cycle of the deleted map. -/
theorem isFaceCycle_lift_of_avoid {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    {L : List M.Dart} (hL : M.IsFaceCycle L)
    (havoid : ∀ x ∈ L, x ≠ a ∧ x ≠ M.alpha a ∧ M.facePerm x ≠ a ∧
      M.facePerm x ≠ M.alpha a)
    {l : List (Dart M a)} (hl : l.map (value M a) = L) :
    (toCombMap M a).IsFaceCycle l := by
  refine isFaceCycle_of_map_value M a hl hL.ne_nil hL.nodup ?_ ?_
  · refine hL.chain.imp_of_mem_imp fun x y hx _ h => ?_
    have h' : M.facePerm x = y := h
    show next M a x = y
    rw [next_of_ne_of_ne M a (havoid x hx).2.2.1 (havoid x hx).2.2.2, h']
  · intro u hu v hv
    have hu' : L.getLast? = some u := hu
    have hv' : L.head? = some v := hv
    have hlast : L.getLast hL.ne_nil = u :=
      Option.some.inj ((List.getLast?_eq_some_getLast hL.ne_nil).symm.trans hu')
    have hhead : L.head hL.ne_nil = v :=
      Option.some.inj ((List.head?_eq_some_head hL.ne_nil).symm.trans hv')
    have hmem : u ∈ L := by
      rw [← hlast]
      exact List.getLast_mem hL.ne_nil
    rw [next_of_ne_of_ne M a (havoid u hmem).2.2.1 (havoid u hmem).2.2.2, ← hlast, ← hhead]
    exact hL.closes

/-- Membership in a lift is membership of the value in the lifted list. -/
theorem mem_of_map_value_eq {M : CombMap.{u}} {a : M.Dart} {l : List (Dart M a)}
    {L : List M.Dart} (hl : l.map (value M a) = L) (x : Dart M a) :
    x ∈ l ↔ value M a x ∈ L := by
  rw [← hl]
  constructor
  · exact List.mem_map_of_mem
  · intro hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
    rwa [value_injective M a hyx] at hy

/-! ## Kept faces -/

theorem exists_keptLift (M : CombMap.{u}) (a : M.Dart) (FB : ∀ g : M.Face, FaceBoundary M g)
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    ∃ l : List (Dart M a), l.map (value M a) = (FB g).darts :=
  exists_map_value_eq M a _ fun d hd =>
    let h := avoid_of_off hg (((FB g).mem_iff d).mp hd)
    ⟨h.1, h.2.1⟩

/-- The lift of the old traversal of a face off both sides of the deleted edge. -/
noncomputable def keptLift (M : CombMap.{u}) (a : M.Dart) (FB : ∀ g : M.Face, FaceBoundary M g)
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) : List (Dart M a) :=
  Classical.choose (exists_keptLift M a FB g hg)

theorem keptLift_map_value {M : CombMap.{u}} {a : M.Dart} (FB : ∀ g : M.Face, FaceBoundary M g)
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    (keptLift M a FB g hg).map (value M a) = (FB g).darts :=
  Classical.choose_spec (exists_keptLift M a FB g hg)

theorem keptLift_map_value_of_eq {M : CombMap.{u}} {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) {g g' : M.Face}
    (hg' : g' ≠ M.faceOf a ∧ g' ≠ M.faceOf (M.alpha a)) (h : g' = g) :
    (keptLift M a FB g' hg').map (value M a) = (FB g).darts := by
  subst h
  exact keptLift_map_value FB g' hg'

theorem keptLift_isFaceCycle {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face)
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    (toCombMap M a).IsFaceCycle (keptLift M a FB g hg) :=
  isFaceCycle_lift_of_avoid (FB g).isFaceCycle
    (fun d hd => avoid_of_off hg (((FB g).mem_iff d).mp hd)) (keptLift_map_value FB g hg)

/-- **A kept face**: the face of the lift of the old traversal of `g`. -/
noncomputable def keptFace (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face)
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) : (toCombMap M a).Face :=
  (toCombMap M a).faceOf ((keptLift M a FB g hg).head (keptLift_isFaceCycle FB g hg).ne_nil)

theorem mem_keptLift_iff {M : CombMap.{u}} {a : M.Dart} (FB : ∀ g : M.Face, FaceBoundary M g)
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) (x : Dart M a) :
    x ∈ keptLift M a FB g hg ↔ M.faceOf (value M a x) = g := by
  rw [mem_of_map_value_eq (keptLift_map_value FB g hg) x]
  exact (FB g).mem_iff (value M a x)

/-- **A surviving dart lies on the kept face of `g` exactly when its old face is `g`.** -/
theorem faceOf_eq_keptFace_iff {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face)
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) (x : Dart M a) :
    (toCombMap M a).faceOf x = keptFace M a FB g hg ↔ M.faceOf (value M a x) = g :=
  ((keptLift_isFaceCycle FB g hg).mem_iff x).symm.trans (mem_keptLift_iff FB g hg x)

theorem faceOf_value_keptLift_head {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face)
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    M.faceOf (value M a ((keptLift M a FB g hg).head (keptLift_isFaceCycle FB g hg).ne_nil)) =
      g :=
  (faceOf_eq_keptFace_iff FB g hg
    ((keptLift M a FB g hg).head (keptLift_isFaceCycle FB g hg).ne_nil)).mp rfl

/-- Kept faces of different old faces are different. -/
theorem keptFace_inj {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    {FB : ∀ g : M.Face, FaceBoundary M g} {g g' : M.Face}
    {hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)}
    {hg' : g' ≠ M.faceOf a ∧ g' ≠ M.faceOf (M.alpha a)}
    (h : keptFace M a FB g hg = keptFace M a FB g' hg') : g = g' :=
  (faceOf_value_keptLift_head FB g hg).symm.trans ((faceOf_eq_keptFace_iff FB g' hg' _).mp h)

theorem keptFace_congr {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) {g g' : M.Face}
    (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a))
    (hg' : g' ≠ M.faceOf a ∧ g' ≠ M.faceOf (M.alpha a)) (h : g = g') :
    keptFace M a FB g hg = keptFace M a FB g' hg' := by
  subst h
  rfl

/-! ## The merged face -/

namespace MergeCycles

/-- **The merged enumeration is nonempty** in a connected map in which some dart survives.
Otherwise both faces are loops of one dart, so vertex rotation swaps the two darts of the
edge, and connectedness leaves no third dart. -/
theorem append_ne_nil {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a)
    (hM : M.IsConnected) (d₀ : Dart M a) : C.xs ++ C.ys ≠ [] := by
  intro hnil
  have hxs : C.xs = [] := (List.append_eq_nil_iff.mp hnil).1
  have hys : C.ys = [] := (List.append_eq_nil_iff.mp hnil).2
  have hfa : M.facePerm a = a := by
    have h := C.facePerm_eq_getD_head_xs
    rw [hxs] at h
    exact h
  have hfαa : M.facePerm (M.alpha a) = M.alpha a := by
    have h := C.facePerm_alpha_eq_getD_head_ys
    rw [hys] at h
    exact h
  have hσa : M.sigma a = M.alpha a := (M.sigma_eq_facePerm_alpha a).trans hfαa
  have hσαa : M.sigma (M.alpha a) = a := by
    rw [M.sigma_eq_facePerm_alpha, M.alpha_involutive a, hfa]
  rcases M.dart_eq_or_alpha_of_swapped_endpoints hM a hσa hσαa (value M a d₀) with h | h
  · exact value_ne M a d₀ h
  · exact value_ne_reverse M a d₀ h

theorem exists_lift {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a) :
    ∃ l : List (Dart M a), l.map (value M a) = C.xs ++ C.ys :=
  exists_map_value_eq M a (C.xs ++ C.ys) fun _ hd => C.avoid hd

/-- A lift of the merged enumeration to the deleted map. -/
noncomputable def lift {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a) :
    List (Dart M a) :=
  Classical.choose C.exists_lift

theorem lift_map_value {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a) :
    C.lift.map (value M a) = C.xs ++ C.ys :=
  Classical.choose_spec C.exists_lift

theorem lift_length {M : CombMap.{u}} {a : M.Dart} (C : MergeCycles M a) :
    C.lift.length = C.xs.length + C.ys.length := by
  have h := congrArg List.length C.lift_map_value
  rw [List.length_map, List.length_append] at h
  exact h

theorem lift_isFaceCycle {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (hne : C.xs ++ C.ys ≠ []) : (toCombMap M a).IsFaceCycle C.lift :=
  C.isFaceCycle_lift hne C.lift_map_value

/-- **The merged face**: the face of the lift of `xs ++ ys`. -/
noncomputable def mergedFace {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (hne : C.xs ++ C.ys ≠ []) : (toCombMap M a).Face :=
  (toCombMap M a).faceOf (C.lift.head (C.lift_isFaceCycle hne).ne_nil)

/-- **A surviving dart lies on the merged face exactly when its old face is one of the two
sides of the deleted edge.** -/
theorem faceOf_eq_mergedFace_iff {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (hne : C.xs ++ C.ys ≠ []) (x : Dart M a) :
    (toCombMap M a).faceOf x = C.mergedFace hne ↔
      M.faceOf (value M a x) = M.faceOf a ∨ M.faceOf (value M a x) = M.faceOf (M.alpha a) :=
  ((C.lift_isFaceCycle hne).mem_iff x).symm.trans
    ((mem_of_map_value_eq C.lift_map_value x).trans
      ⟨C.faceOf_of_mem_append,
        fun h => C.mem_append_of_faceOf h (value_ne M a x) (value_ne_reverse M a x)⟩)

/-- A kept face is not the merged face. -/
theorem keptFace_ne_mergedFace {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ [])
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    keptFace M a FB g hg ≠ C.mergedFace hne := by
  intro h
  have hx := faceOf_value_keptLift_head FB g hg
  rcases (C.faceOf_eq_mergedFace_iff hne
      ((keptLift M a FB g hg).head (keptLift_isFaceCycle FB g hg).ne_nil)).mp h with hc | hc
  · exact hg.1 (hx.symm.trans hc)
  · exact hg.2 (hx.symm.trans hc)

/-- **Every face of the deleted map is the merged face or a kept face.** -/
theorem face_cases {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart} (C : MergeCycles M a)
    (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ [])
    (F : (toCombMap M a).Face) :
    F = C.mergedFace hne ∨
      ∃ g : M.Face, ∃ hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a),
        F = keptFace M a FB g hg := by
  obtain ⟨x, rfl⟩ : ∃ x, (toCombMap M a).faceOf x = F := Quotient.exists_rep F
  by_cases hm : M.faceOf (value M a x) = M.faceOf a ∨
      M.faceOf (value M a x) = M.faceOf (M.alpha a)
  · exact Or.inl ((C.faceOf_eq_mergedFace_iff hne x).mpr hm)
  · obtain ⟨h1, h2⟩ := not_or.mp hm
    exact Or.inr ⟨M.faceOf (value M a x), ⟨h1, h2⟩,
      (faceOf_eq_keptFace_iff FB (M.faceOf (value M a x)) ⟨h1, h2⟩ x).mpr rfl⟩

/-- The traversal of a face known to be a kept face: the lift of the old traversal. -/
noncomputable def keptBoundary {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) {F : (toCombMap M a).Face}
    (hk : ∃ g : M.Face, ∃ hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a),
      F = keptFace M a FB g hg) :
    FaceBoundary (toCombMap M a) F :=
  (congrArg (FaceBoundary (toCombMap M a))
      (Classical.choose_spec (Classical.choose_spec hk))).mpr
    (keptLift_isFaceCycle FB (Classical.choose hk)
      (Classical.choose (Classical.choose_spec hk))).toFaceBoundary

theorem keptBoundary_map_value {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (FB : ∀ g : M.Face, FaceBoundary M g) {F : (toCombMap M a).Face}
    (hk : ∃ g : M.Face, ∃ hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a),
      F = keptFace M a FB g hg)
    {g : M.Face} (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a))
    (hF : F = keptFace M a FB g hg) :
    (keptBoundary FB hk).darts.map (value M a) = (FB g).darts := by
  have h1 : (keptBoundary FB hk).darts =
      keptLift M a FB (Classical.choose hk) (Classical.choose (Classical.choose_spec hk)) :=
    (FaceBoundary.darts_mpr (Classical.choose_spec (Classical.choose_spec hk)) _).trans
      (CombMap.IsFaceCycle.toFaceBoundary_darts _)
  exact (congrArg (List.map (value M a)) h1).trans (keptLift_map_value_of_eq FB _
    (keptFace_inj ((Classical.choose_spec (Classical.choose_spec hk)).symm.trans hF)))

/-- **A traversal of every face of the deleted map.** -/
noncomputable def faceBoundary {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ [])
    (F : (toCombMap M a).Face) : FaceBoundary (toCombMap M a) F := by
  classical
  exact if hF : F = C.mergedFace hne then
      (congrArg (FaceBoundary (toCombMap M a)) hF).mpr (C.lift_isFaceCycle hne).toFaceBoundary
    else keptBoundary FB ((C.face_cases FB hne F).resolve_left hF)

/-- The merged face reads the lift of the merged enumeration. -/
theorem faceBoundary_mergedFace_darts {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ []) :
    (C.faceBoundary FB hne (C.mergedFace hne)).darts = C.lift := by
  rw [faceBoundary, dif_pos rfl]
  exact (FaceBoundary.darts_mpr (rfl : C.mergedFace hne = C.mergedFace hne) _).trans
    (CombMap.IsFaceCycle.toFaceBoundary_darts _)

theorem faceBoundary_mergedFace_map_value {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ []) :
    (C.faceBoundary FB hne (C.mergedFace hne)).darts.map (value M a) = C.xs ++ C.ys := by
  rw [C.faceBoundary_mergedFace_darts FB hne, C.lift_map_value]

/-- A kept face reads the lift of the old traversal. -/
theorem faceBoundary_keptFace_map_value {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.xs ++ C.ys ≠ [])
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    (C.faceBoundary FB hne (keptFace M a FB g hg)).darts.map (value M a) = (FB g).darts := by
  rw [faceBoundary, dif_neg (C.keptFace_ne_mergedFace FB hne g hg)]
  exact keptBoundary_map_value FB _ hg rfl

/-- **Exactly one face disappears.** -/
theorem faceCount_add_one {M : CombMap.{u}} [DecidableEq M.Dart] {a : M.Dart}
    (C : MergeCycles M a) (hM : M.IsConnected) (d₀ : Dart M a) :
    (toCombMap M a).faceCount + 1 = M.faceCount := by
  have hbal := faceCount_balance_of_neFace M a C.face_ne
  have hv := vertexCount_eq_of_neFace M a hM d₀ C.face_ne
  omega

end MergeCycles

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.darts_mpr
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.exists_isFaceCycle_cons
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.isFaceCycle_lift_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.faceOf_eq_keptFace_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.keptFace_inj
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.append_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceOf_eq_mergedFace_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.keptFace_ne_mergedFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceBoundary_mergedFace_map_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceBoundary_keptFace_map_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.MergeCycles.faceCount_add_one
