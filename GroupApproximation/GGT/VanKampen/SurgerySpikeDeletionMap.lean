import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeMap
import GroupApproximation.GGT.VanKampen.SpikeDeletion
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces of a map after deleting a spike

The map layer of the spike deletion surgery.  Let `a` be the tip of a spike, a dart fixed by
the vertex rotation.  The face rotation then takes `alpha a` back to `a`, so both sides of the
edge lie on one face, which reads `alpha a :: a :: rest` from the edge
(`EdgeDeletion.SpikeCycle`, `EdgeDeletion.spikeCycleOf`).  Deleting the edge of `a` gives
`EdgeDeletion.toCombMap M a`, and this file names its faces and allocates a traversal of each
of them.

* `SpikeCycle.rest_ne_nil`: in a connected map where some dart survives, the rest of the face
  is nonempty.
* `SpikeCycle.shrunkFace`: the face of the lift of `rest` (`faceOf_eq_shrunkFace_iff`: a
  surviving dart lies on it exactly when its old face is the face of `a`).
* `SpikeCycle.face_cases`: every face of the deleted map is the shrunk face or a kept face
  (`EdgeDeletion.keptFace`).
* `SpikeCycle.faceBoundary`: a traversal of every face; the shrunk face reads the lift of
  `rest` (`faceBoundary_shrunkFace_map_value`) and a kept face reads the lift of the old
  traversal (`faceBoundary_keptFace_map_value`).
* `SpikeCycle.faceCount_eq`: in a planar map no face disappears.

Each deletion lowers the number of darts by two (`EdgeDeletion.dartCount_add_two`); this is
the descent step of Case 2 in the proof of Osin's Lemma 9.4, measured by dart count.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace EdgeDeletion

/-- At the tip of a spike the face rotation takes the reverse dart back to the tip. -/
theorem facePerm_alpha_of_fixed {M : CombMap.{u}} {a : M.Dart} (ha : M.sigma a = a) :
    M.facePerm (M.alpha a) = a :=
  (M.sigma_eq_facePerm_alpha a).symm.trans ha

/-- **The face around a spike**, enumerated from the edge: the reverse of the tip, the tip,
and the rest of the face. -/
structure SpikeCycle (M : CombMap.{u}) (a : M.Dart) where
  /-- The face after the tip. -/
  rest : List M.Dart
  /-- The face of the spike. -/
  cyc : M.IsFaceCycle (M.alpha a :: a :: rest)

theorem exists_spikeCycle (M : CombMap.{u}) (a : M.Dart) (ha : M.sigma a = a) :
    ∃ rest : List M.Dart, M.IsFaceCycle (M.alpha a :: a :: rest) := by
  obtain ⟨l, hl⟩ := exists_isFaceCycle_cons M (M.alpha a)
  cases l with
  | nil =>
      have h : M.facePerm (M.alpha a) = M.alpha a := hl.closes
      exact absurd (h.symm.trans (facePerm_alpha_of_fixed ha)) (M.alpha_fixedPointFree a)
  | cons x rest =>
      have hx : M.facePerm (M.alpha a) = x := (List.isChain_cons.mp hl.chain).1 x rfl
      have hxa : x = a := hx.symm.trans (facePerm_alpha_of_fixed ha)
      subst hxa
      exact ⟨rest, hl⟩

/-- **The face around a spike tip.** -/
noncomputable def spikeCycleOf (M : CombMap.{u}) (a : M.Dart) (ha : M.sigma a = a) :
    SpikeCycle M a where
  rest := Classical.choose (exists_spikeCycle M a ha)
  cyc := Classical.choose_spec (exists_spikeCycle M a ha)

namespace SpikeCycle

variable {M : CombMap.{u}} {a : M.Dart} (C : SpikeCycle M a)

include C in
/-- The face rotation takes the reverse of the tip to the tip. -/
theorem facePerm_alpha : M.facePerm (M.alpha a) = a :=
  (List.isChain_cons.mp C.cyc.chain).1 a rfl

include C in
/-- The tip is fixed by the vertex rotation. -/
theorem sigma_eq : M.sigma a = a :=
  (M.sigma_eq_facePerm_alpha a).trans C.facePerm_alpha

include C in
/-- Both sides of the edge lie on one face. -/
theorem faceOf_alpha : M.faceOf (M.alpha a) = M.faceOf a :=
  (M.faceOf_facePerm (M.alpha a)).symm.trans (congrArg M.faceOf C.facePerm_alpha)

theorem ne_of_mem_rest {d : M.Dart} (hd : d ∈ C.rest) : d ≠ a := by
  rintro rfl
  exact (List.nodup_cons.mp (List.nodup_cons.mp C.cyc.nodup).2).1 hd

theorem ne_alpha_of_mem_rest {d : M.Dart} (hd : d ∈ C.rest) : d ≠ M.alpha a := by
  rintro rfl
  exact (List.nodup_cons.mp C.cyc.nodup).1 (List.mem_cons_of_mem a hd)

theorem nodup_rest : C.rest.Nodup :=
  (List.nodup_cons.mp (List.nodup_cons.mp C.cyc.nodup).2).2

theorem faceOf_of_mem_rest {d : M.Dart} (hd : d ∈ C.rest) : M.faceOf d = M.faceOf a :=
  ((C.cyc.mem_iff d).mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem a hd))).trans
    C.faceOf_alpha

theorem mem_rest_of_faceOf {d : M.Dart} (hd : M.faceOf d = M.faceOf a) (h1 : d ≠ a)
    (h2 : d ≠ M.alpha a) : d ∈ C.rest := by
  rcases List.mem_cons.mp ((C.cyc.mem_iff d).mpr (hd.trans C.faceOf_alpha.symm)) with h | h
  · exact absurd h h2
  · rcases List.mem_cons.mp h with h' | h'
    · exact absurd h' h1
    · exact h'

/-- The last dart of the face returns to the reverse of the tip. -/
theorem facePerm_getD_last : M.facePerm (C.rest.getLast?.getD a) = M.alpha a := by
  have h := C.cyc.closes
  rw [getLast_cons_eq_getD, List.getLast?_cons, Option.getD_some] at h
  exact h

/-- The successor of the tip heads the rest of the face. -/
theorem facePerm_eq_getD_head : M.facePerm a = C.rest.head?.getD (M.alpha a) := by
  have hlast := C.facePerm_getD_last
  have hchain := (List.isChain_cons.mp (List.isChain_cons.mp C.cyc.chain).2).1
  revert hlast hchain
  cases C.rest with
  | nil => exact fun h _ => h
  | cons y t => exact fun _ h => h y rfl

/-- **The rest of the face is nonempty** in a connected map in which some dart survives.
Otherwise the face reads `alpha a, a`, so vertex rotation fixes both darts of the edge, and
connectedness leaves no third dart. -/
theorem rest_ne_nil (hM : M.IsConnected) (d₀ : Dart M a) : C.rest ≠ [] := by
  intro hnil
  have hfa : M.facePerm a = M.alpha a := by
    have h := C.facePerm_getD_last
    rw [hnil] at h
    exact h
  have hσ : M.sigma (M.alpha a) = M.alpha a := by
    rw [M.sigma_eq_facePerm_alpha, M.alpha_involutive a, hfa]
  exact not_both_fixed M a hM d₀ ⟨C.sigma_eq, hσ⟩

theorem exists_lift : ∃ l : List (Dart M a), l.map (value M a) = C.rest :=
  exists_map_value_eq M a C.rest fun _ hd => ⟨C.ne_of_mem_rest hd, C.ne_alpha_of_mem_rest hd⟩

/-- A lift of the rest of the face to the deleted map. -/
noncomputable def lift : List (Dart M a) :=
  Classical.choose C.exists_lift

theorem lift_map_value : C.lift.map (value M a) = C.rest :=
  Classical.choose_spec C.exists_lift

variable [DecidableEq M.Dart]

/-- The rest of the face follows `next`. -/
theorem isChain_next : C.rest.IsChain (fun d e => next M a d = e) :=
  (List.isChain_cons.mp (List.isChain_cons.mp C.cyc.chain).2).2.imp_of_mem_imp
    fun d e _ he h => by
      have h' : M.facePerm d = e := h
      have h1 : M.facePerm d ≠ a := by rw [h']; exact C.ne_of_mem_rest he
      have h2 : M.facePerm d ≠ M.alpha a := by rw [h']; exact C.ne_alpha_of_mem_rest he
      show next M a d = e
      rw [next_of_ne_of_ne M a h1 h2, h']

/-- The rest of the face closes up under `next`. -/
theorem next_last_eq_head :
    ∀ u ∈ C.rest.getLast?, ∀ v ∈ C.rest.head?, next M a u = v := by
  intro u hu v hv
  have hlast := C.facePerm_getD_last
  have hhead := C.facePerm_eq_getD_head
  have hu' : C.rest.getLast? = some u := hu
  have hv' : C.rest.head? = some v := hv
  rw [hu'] at hlast
  rw [hv'] at hhead
  have hlast' : M.facePerm u = M.alpha a := hlast
  have hhead' : M.facePerm a = v := hhead
  have hne1 : M.facePerm u ≠ a := by
    rw [hlast']
    exact M.alpha_fixedPointFree a
  have hne2 : M.facePerm a ≠ a := by
    rw [hhead']
    exact C.ne_of_mem_rest (List.mem_of_mem_head? hv)
  rw [next, if_neg hne1, if_pos hlast', if_neg hne2, hhead']

/-- **The shrunk face.**  The lift of the rest of the face is a face cycle of the deleted
map. -/
theorem lift_isFaceCycle (hne : C.rest ≠ []) : (toCombMap M a).IsFaceCycle C.lift :=
  isFaceCycle_of_map_value M a C.lift_map_value hne C.nodup_rest C.isChain_next
    C.next_last_eq_head

/-- **The shrunk face**: the face of the lift of the rest of the face. -/
noncomputable def shrunkFace (hne : C.rest ≠ []) : (toCombMap M a).Face :=
  (toCombMap M a).faceOf (C.lift.head (C.lift_isFaceCycle hne).ne_nil)

/-- **A surviving dart lies on the shrunk face exactly when its old face is the face of the
spike.** -/
theorem faceOf_eq_shrunkFace_iff (hne : C.rest ≠ []) (x : Dart M a) :
    (toCombMap M a).faceOf x = C.shrunkFace hne ↔ M.faceOf (value M a x) = M.faceOf a :=
  ((C.lift_isFaceCycle hne).mem_iff x).symm.trans
    ((mem_of_map_value_eq C.lift_map_value x).trans
      ⟨C.faceOf_of_mem_rest,
        fun h => C.mem_rest_of_faceOf h (value_ne M a x) (value_ne_reverse M a x)⟩)

/-- A kept face is not the shrunk face. -/
theorem keptFace_ne_shrunkFace (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.rest ≠ [])
    (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    keptFace M a FB g hg ≠ C.shrunkFace hne := fun h =>
  hg.1 ((faceOf_value_keptLift_head FB g hg).symm.trans ((C.faceOf_eq_shrunkFace_iff hne
    ((keptLift M a FB g hg).head (keptLift_isFaceCycle FB g hg).ne_nil)).mp h))

/-- **Every face of the deleted map is the shrunk face or a kept face.** -/
theorem face_cases (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.rest ≠ [])
    (F : (toCombMap M a).Face) :
    F = C.shrunkFace hne ∨
      ∃ g : M.Face, ∃ hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a),
        F = keptFace M a FB g hg := by
  obtain ⟨x, rfl⟩ : ∃ x, (toCombMap M a).faceOf x = F := Quotient.exists_rep F
  by_cases hm : M.faceOf (value M a x) = M.faceOf a
  · exact Or.inl ((C.faceOf_eq_shrunkFace_iff hne x).mpr hm)
  · have hg : M.faceOf (value M a x) ≠ M.faceOf a ∧
        M.faceOf (value M a x) ≠ M.faceOf (M.alpha a) :=
      ⟨hm, fun h => hm (h.trans C.faceOf_alpha)⟩
    exact Or.inr ⟨M.faceOf (value M a x), hg, (faceOf_eq_keptFace_iff FB _ hg x).mpr rfl⟩

/-- **A traversal of every face of the deleted map.** -/
noncomputable def faceBoundary (FB : ∀ g : M.Face, FaceBoundary M g) (hne : C.rest ≠ [])
    (F : (toCombMap M a).Face) : FaceBoundary (toCombMap M a) F := by
  classical
  exact if hF : F = C.shrunkFace hne then
      (congrArg (FaceBoundary (toCombMap M a)) hF).mpr (C.lift_isFaceCycle hne).toFaceBoundary
    else MergeCycles.keptBoundary FB ((C.face_cases FB hne F).resolve_left hF)

/-- The shrunk face reads the lift of the rest of the face. -/
theorem faceBoundary_shrunkFace_darts (FB : ∀ g : M.Face, FaceBoundary M g)
    (hne : C.rest ≠ []) : (C.faceBoundary FB hne (C.shrunkFace hne)).darts = C.lift := by
  rw [faceBoundary, dif_pos rfl]
  exact (FaceBoundary.darts_mpr (rfl : C.shrunkFace hne = C.shrunkFace hne) _).trans
    (CombMap.IsFaceCycle.toFaceBoundary_darts _)

theorem faceBoundary_shrunkFace_map_value (FB : ∀ g : M.Face, FaceBoundary M g)
    (hne : C.rest ≠ []) :
    (C.faceBoundary FB hne (C.shrunkFace hne)).darts.map (value M a) = C.rest := by
  rw [C.faceBoundary_shrunkFace_darts FB hne, C.lift_map_value]

/-- A kept face reads the lift of the old traversal. -/
theorem faceBoundary_keptFace_map_value (FB : ∀ g : M.Face, FaceBoundary M g)
    (hne : C.rest ≠ []) (g : M.Face) (hg : g ≠ M.faceOf a ∧ g ≠ M.faceOf (M.alpha a)) :
    (C.faceBoundary FB hne (keptFace M a FB g hg)).darts.map (value M a) = (FB g).darts := by
  rw [faceBoundary, dif_neg (C.keptFace_ne_shrunkFace FB hne g hg)]
  exact MergeCycles.keptBoundary_map_value FB _ hg rfl

include C in
/-- **Deleting a spike from a planar map keeps the number of faces**, provided some dart
survives: both sides of the edge lie on one face, and the tip vertex disappears with the
edge. -/
theorem faceCount_eq (hM : M.IsPlanar) (d₀ : Dart M a) :
    (toCombMap M a).faceCount = M.faceCount := by
  have hN := planar_of_sigma_fixed M a hM C.sigma_eq d₀
  have hbal := faceCount_balance_of_sameFace M a C.faceOf_alpha.symm
  have hedge := edgeCount_add_one M a
  have hE := M.euler_eq_two hM
  have hEN := (toCombMap M a).euler_eq_two hN
  omega

end SpikeCycle

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.exists_spikeCycle
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.rest_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.lift_isFaceCycle
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.faceOf_eq_shrunkFace_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.faceBoundary_shrunkFace_map_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.faceBoundary_keptFace_map_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.SpikeCycle.faceCount_eq
