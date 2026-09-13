import GroupApproximation.GGT.SystolicDiscMirrorFoldRestrict
import GroupApproximation.GGT.VanKampen.PinchLemma
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# The pinched mirror fold (HC6)

Let `δ, alpha δ` be an edge between two inner triangles of a stage, and let the darts two steps
after `δ` and after `alpha δ` along their faces start at one vertex.  Deleting the edge turns
the two triangles into a square `e1, e2, f1, f2`, with `e1 = facePerm δ` and
`f1 = facePerm (alpha δ)`; the corners `alpha e1` and `alpha f1` lie at that vertex.
Splitting the vertex between these corners (`FoldMap.joined`) cuts the map into two pieces
of total Euler characteristic four, with two pending digons `e2, f1` and `e1, f2`, one in each
piece.  The piece carrying the exterior face, with its digon deleted, is a triangulated disc
with the same boundary and three faces fewer.

* `FoldStage.IsPinch`: the configuration.
* `FoldStage.IsPinch.pinchStage`: the split stage, with the boundary of the stage
  (`pinchStage_boundary`) and as many faces (`pinchStage_faceCount`).
* `FoldStage.exists_disc_of_pinch`: the smaller disc.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

namespace FoldStage

open scoped Classical

/-- Face rotation moves every dart of a stage: an edge of `X` joins distinct vertices. -/
theorem facePerm_ne_self (S : FoldStage X) (z : S.map.Dart) : S.map.facePerm z ≠ z :=
  fun hz => (S.adj z).ne ((congrArg S.lab hz).symm.trans (S.lab_facePerm z))

/-- Two face rotations stay on the face. -/
theorem faceOf_facePerm_two (S : FoldStage X) (z : S.map.Dart) :
    S.map.faceOf (S.map.facePerm (S.map.facePerm z)) = S.map.faceOf z :=
  (S.map.faceOf_facePerm _).trans (S.map.faceOf_facePerm z)

/-- The exterior cycle lies on the side of a dart reaching its head. -/
theorem reachSide_of_head (S : FoldStage X) {c : S.map.Dart}
    (hc : reachSide S.map c (S.cyc.head S.isFaceCycle.ne_nil)) :
    ∀ z ∈ S.cyc, reachSide S.map c z := fun z hz =>
  Relation.EqvGen.trans _ _ _ hc
    (PinchLemma.eqvGen_of_faceOf_eq ((S.isFaceCycle.mem_iff z).mp hz).symm)

/-- **The pinch configuration** at `δ`: a planar stage with nothing pending, `δ` and
`alpha δ` off the exterior cycle on distinct faces, and the darts two steps after them along
their faces at one vertex. -/
structure IsPinch (S : FoldStage X) (δ : S.map.Dart) : Prop where
  planar : S.map.IsPlanar
  good : ∀ z, ¬ S.bad z
  not_mem : δ ∉ S.cyc
  not_mem_alpha : S.map.alpha δ ∉ S.cyc
  face_ne : S.map.faceOf δ ≠ S.map.faceOf (S.map.alpha δ)
  pinch : S.map.sigma.SameCycle (S.map.facePerm (S.map.facePerm δ))
    (S.map.facePerm (S.map.facePerm (S.map.alpha δ)))

/-- The map with the edge of `δ` deleted. -/
noncomputable abbrev delMap (S : FoldStage X) (δ : S.map.Dart) : CombMap.{0} :=
  EdgeDeletion.toCombMap S.map δ

namespace IsPinch

variable {S : FoldStage X} {δ : S.map.Dart}

/-! ### The two triangles -/

theorem back (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm (S.map.facePerm δ)) = δ := by
  have h3 := (S.tri δ h.not_mem (h.good δ)).1
  rwa [perm_pow_three_apply] at h3

theorem back_alpha (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm (S.map.facePerm (S.map.alpha δ))) = S.map.alpha δ := by
  have h3 := (S.tri _ h.not_mem_alpha (h.good _)).1
  rwa [perm_pow_three_apply] at h3

theorem e1_not_mem (h : IsPinch S δ) : S.map.facePerm δ ∉ S.cyc := fun hm =>
  h.not_mem ((isFaceCycle_facePerm_mem_iff S.isFaceCycle δ).mp hm)

theorem e2_not_mem (h : IsPinch S δ) : S.map.facePerm (S.map.facePerm δ) ∉ S.cyc := fun hm =>
  h.e1_not_mem ((isFaceCycle_facePerm_mem_iff S.isFaceCycle _).mp hm)

theorem f1_not_mem (h : IsPinch S δ) : S.map.facePerm (S.map.alpha δ) ∉ S.cyc := fun hm =>
  h.not_mem_alpha ((isFaceCycle_facePerm_mem_iff S.isFaceCycle _).mp hm)

theorem f2_not_mem (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm (S.map.alpha δ)) ∉ S.cyc := fun hm =>
  h.f1_not_mem ((isFaceCycle_facePerm_mem_iff S.isFaceCycle _).mp hm)

/-- Darts on the face of `δ` differ from darts on the face of `alpha δ`. -/
theorem ne_of_faceOf (h : IsPinch S δ) {x y : S.map.Dart}
    (hx : S.map.faceOf x = S.map.faceOf δ)
    (hy : S.map.faceOf y = S.map.faceOf (S.map.alpha δ)) : x ≠ y := fun hxy =>
  h.face_ne (hx.symm.trans ((congrArg S.map.faceOf hxy).trans hy))

theorem e1_ne_alpha (h : IsPinch S δ) : S.map.facePerm δ ≠ S.map.alpha δ :=
  h.ne_of_faceOf (S.map.faceOf_facePerm δ) rfl

theorem e2_ne (h : IsPinch S δ) : S.map.facePerm (S.map.facePerm δ) ≠ δ := fun he =>
  S.facePerm_ne_self δ (by have hb := h.back; rwa [he] at hb)

theorem e2_ne_alpha (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm δ) ≠ S.map.alpha δ :=
  h.ne_of_faceOf (S.faceOf_facePerm_two δ) rfl

theorem f1_ne (h : IsPinch S δ) : S.map.facePerm (S.map.alpha δ) ≠ δ :=
  (h.ne_of_faceOf rfl (S.map.faceOf_facePerm (S.map.alpha δ))).symm

theorem f2_ne (h : IsPinch S δ) : S.map.facePerm (S.map.facePerm (S.map.alpha δ)) ≠ δ :=
  (h.ne_of_faceOf rfl (S.faceOf_facePerm_two (S.map.alpha δ))).symm

theorem f2_ne_alpha (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm (S.map.alpha δ)) ≠ S.map.alpha δ := fun he =>
  S.facePerm_ne_self (S.map.alpha δ) (by have hb := h.back_alpha; rwa [he] at hb)

theorem e1_ne_f1 (h : IsPinch S δ) : S.map.facePerm δ ≠ S.map.facePerm (S.map.alpha δ) :=
  h.ne_of_faceOf (S.map.faceOf_facePerm δ) (S.map.faceOf_facePerm (S.map.alpha δ))

theorem e2_ne_f1 (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm δ) ≠ S.map.facePerm (S.map.alpha δ) :=
  h.ne_of_faceOf (S.faceOf_facePerm_two δ) (S.map.faceOf_facePerm (S.map.alpha δ))

theorem f2_ne_e1 (h : IsPinch S δ) :
    S.map.facePerm (S.map.facePerm (S.map.alpha δ)) ≠ S.map.facePerm δ :=
  (h.ne_of_faceOf (S.map.faceOf_facePerm δ) (S.faceOf_facePerm_two (S.map.alpha δ))).symm

/-! ### The deleted map -/

/-- The dart after `δ` along its face, in the deleted map. -/
noncomputable def e1 (h : IsPinch S δ) : (S.delMap δ).Dart :=
  EdgeDeletion.ofValue S.map δ (S.map.facePerm δ) (S.facePerm_ne_self δ) h.e1_ne_alpha

/-- The dart two steps after `δ` along its face, in the deleted map. -/
noncomputable def e2 (h : IsPinch S δ) : (S.delMap δ).Dart :=
  EdgeDeletion.ofValue S.map δ (S.map.facePerm (S.map.facePerm δ)) h.e2_ne h.e2_ne_alpha

/-- The dart after `alpha δ` along its face, in the deleted map. -/
noncomputable def f1 (h : IsPinch S δ) : (S.delMap δ).Dart :=
  EdgeDeletion.ofValue S.map δ (S.map.facePerm (S.map.alpha δ)) h.f1_ne
    (S.facePerm_ne_self (S.map.alpha δ))

/-- The dart two steps after `alpha δ` along its face, in the deleted map. -/
noncomputable def f2 (h : IsPinch S δ) : (S.delMap δ).Dart :=
  EdgeDeletion.ofValue S.map δ (S.map.facePerm (S.map.facePerm (S.map.alpha δ))) h.f2_ne
    h.f2_ne_alpha

theorem next_e1 (h : IsPinch S δ) :
    EdgeDeletion.next S.map δ (S.map.facePerm δ) = S.map.facePerm (S.map.facePerm δ) :=
  EdgeDeletion.next_of_ne_of_ne S.map δ h.e2_ne h.e2_ne_alpha

theorem next_e2 (h : IsPinch S δ) :
    EdgeDeletion.next S.map δ (S.map.facePerm (S.map.facePerm δ)) =
      S.map.facePerm (S.map.alpha δ) := by
  rw [EdgeDeletion.next, if_pos h.back, if_neg (S.facePerm_ne_self (S.map.alpha δ))]

theorem next_f1 (h : IsPinch S δ) :
    EdgeDeletion.next S.map δ (S.map.facePerm (S.map.alpha δ)) =
      S.map.facePerm (S.map.facePerm (S.map.alpha δ)) :=
  EdgeDeletion.next_of_ne_of_ne S.map δ h.f2_ne h.f2_ne_alpha

theorem next_f2 (h : IsPinch S δ) :
    EdgeDeletion.next S.map δ (S.map.facePerm (S.map.facePerm (S.map.alpha δ))) =
      S.map.facePerm δ := by
  have h1 : S.map.facePerm (S.map.facePerm (S.map.facePerm (S.map.alpha δ))) ≠ δ := by
    rw [h.back_alpha]
    exact S.map.alpha_fixedPointFree δ
  rw [EdgeDeletion.next, if_neg h1, if_pos h.back_alpha, if_neg (S.facePerm_ne_self δ)]

theorem del_e1 (h : IsPinch S δ) : (S.delMap δ).facePerm h.e1 = h.e2 :=
  (EdgeDeletion.facePerm_eq_iff S.map δ h.e1 h.e2).mpr h.next_e1

theorem del_e2 (h : IsPinch S δ) : (S.delMap δ).facePerm h.e2 = h.f1 :=
  (EdgeDeletion.facePerm_eq_iff S.map δ h.e2 h.f1).mpr h.next_e2

theorem del_f1 (h : IsPinch S δ) : (S.delMap δ).facePerm h.f1 = h.f2 :=
  (EdgeDeletion.facePerm_eq_iff S.map δ h.f1 h.f2).mpr h.next_f1

theorem del_f2 (h : IsPinch S δ) : (S.delMap δ).facePerm h.f2 = h.e1 :=
  (EdgeDeletion.facePerm_eq_iff S.map δ h.f2 h.e1).mpr h.next_f2

theorem e1_ne_f1' (h : IsPinch S δ) : h.e1 ≠ h.f1 := fun he =>
  h.e1_ne_f1 (congrArg (EdgeDeletion.value S.map δ) he)

theorem e2_ne_f1' (h : IsPinch S δ) : h.e2 ≠ h.f1 := fun he =>
  h.e2_ne_f1 (congrArg (EdgeDeletion.value S.map δ) he)

theorem e2_ne_e1' (h : IsPinch S δ) : h.e2 ≠ h.e1 := fun he =>
  S.facePerm_ne_self (S.map.facePerm δ) (congrArg (EdgeDeletion.value S.map δ) he)

theorem f2_ne_e1' (h : IsPinch S δ) : h.f2 ≠ h.e1 := fun he =>
  h.f2_ne_e1 (congrArg (EdgeDeletion.value S.map δ) he)

theorem f2_ne_f1' (h : IsPinch S δ) : h.f2 ≠ h.f1 := fun he =>
  S.facePerm_ne_self (S.map.facePerm (S.map.alpha δ)) (congrArg (EdgeDeletion.value S.map δ) he)

/-- In the deleted map `e1` and `f1` lie on one face, the square. -/
theorem del_face (h : IsPinch S δ) :
    (S.delMap δ).faceOf h.e1 = (S.delMap δ).faceOf h.f1 := by
  rw [← h.del_e2, ← h.del_e1, CombMap.faceOf_facePerm, CombMap.faceOf_facePerm]

/-- In the deleted map `alpha e1` and `alpha f1` start at one vertex. -/
theorem del_pinch (h : IsPinch S δ) :
    (S.delMap δ).sigma.SameCycle ((S.delMap δ).alpha h.e1) ((S.delMap δ).alpha h.f1) := by
  have hv : S.map.vertexOf (S.map.alpha (S.map.facePerm δ)) =
      S.map.vertexOf (S.map.alpha (S.map.facePerm (S.map.alpha δ))) :=
    (Systolic.vertexOf_facePerm S.map _).symm.trans
      (((CombMap.vertexOf_eq_iff _ _ _).mpr h.pinch).trans (Systolic.vertexOf_facePerm S.map _))
  have he : EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.e1) =
      S.map.alpha (S.map.facePerm δ) := EdgeDeletion.alpha_val S.map δ h.e1
  have hf : EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.f1) =
      S.map.alpha (S.map.facePerm (S.map.alpha δ)) := EdgeDeletion.alpha_val S.map δ h.f1
  exact (CombMap.vertexOf_eq_iff _ _ _).mp ((EdgeDeletion.vertexOf_eq_iff S.map δ _ _).mpr
    ((congrArg S.map.vertexOf he).trans (hv.trans (congrArg S.map.vertexOf hf).symm)))

theorem del_planar (h : IsPinch S δ) : (S.delMap δ).IsPlanar :=
  EdgeDeletion.planar_of_neFace S.map δ h.planar h.e1 h.face_ne

theorem del_faceCount (h : IsPinch S δ) : (S.delMap δ).faceCount + 1 = S.map.faceCount := by
  have hb := EdgeDeletion.faceCount_balance_of_neFace S.map δ h.face_ne
  have hv := EdgeDeletion.vertexCount_eq_of_neFace S.map δ h.planar.1 h.e1 h.face_ne
  show (EdgeDeletion.toCombMap S.map δ).faceCount + 1 = S.map.faceCount
  omega

/-! ### The split map -/

/-- The deleted map with the vertex of `alpha e1` and `alpha f1` split between these corners. -/
noncomputable abbrev splitMap (h : IsPinch S δ) : CombMap.{0} :=
  FoldMap.joined (S.delMap δ) h.e1 h.f1

theorem joined_euler (h : IsPinch S δ) : h.splitMap.eulerCharacteristic = 4 :=
  PinchLemma.split_euler h.del_planar h.e1_ne_f1' h.del_face h.del_pinch

theorem joined_faceCount (h : IsPinch S δ) : h.splitMap.faceCount = S.map.faceCount := by
  have hne : (S.delMap δ).alpha ((S.delMap δ).alpha h.e1) ≠
      (S.delMap δ).alpha ((S.delMap δ).alpha h.f1) := by
    rw [(S.delMap δ).alpha_involutive h.e1, (S.delMap δ).alpha_involutive h.f1]
    exact h.e1_ne_f1'
  have hface : (S.delMap δ).facePerm.SameCycle ((S.delMap δ).alpha ((S.delMap δ).alpha h.e1))
      ((S.delMap δ).alpha ((S.delMap δ).alpha h.f1)) := by
    rw [(S.delMap δ).alpha_involutive h.e1, (S.delMap δ).alpha_involutive h.f1,
      ← CombMap.faceOf_eq_iff]
    exact h.del_face
  exact (VertexJoin.faceCount_eq (S.delMap δ) _ _ hne hface).trans h.del_faceCount

theorem joined_fp_e1 (h : IsPinch S δ) : h.splitMap.facePerm h.e1 = h.f2 := by
  rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_left, h.del_f1]

theorem joined_fp_e2 (h : IsPinch S δ) : h.splitMap.facePerm h.e2 = h.f1 :=
  PinchLemma.split_facePerm_d h.del_e2 h.e2_ne_f1' h.e2_ne_e1'

theorem joined_fp_f1 (h : IsPinch S δ) : h.splitMap.facePerm h.f1 = h.e2 := by
  rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_right, h.del_e1]

theorem joined_fp_f2 (h : IsPinch S δ) : h.splitMap.facePerm h.f2 = h.e1 := by
  rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne h.f2_ne_e1' h.f2_ne_f1',
    h.del_f2]

/-- Every dart of the split map is reached from `e2` or from `e1`. -/
theorem reach (h : IsPinch S δ) (x : h.splitMap.Dart) :
    reachSide h.splitMap h.e2 x ∨ reachSide h.splitMap h.e1 x :=
  PinchLemma.reach_or_reach h.del_planar.1 h.del_e1 h.del_e2 h.e2_ne_f1' h.e2_ne_e1' x

/-- In the split map `e1` is not reached from `e2`. -/
theorem not_reach (h : IsPinch S δ) : ¬ reachSide h.splitMap h.e2 h.e1 :=
  PinchLemma.not_reach_p h.del_planar h.del_e1 h.del_e2 h.e2_ne_f1' h.e2_ne_e1' h.e1_ne_f1'
    h.del_face h.del_pinch

theorem reach_e1_f2 (h : IsPinch S δ) : reachSide h.splitMap h.e1 h.f2 := by
  have hr := PinchLemma.eqvGen_facePerm (M := h.splitMap) h.e1
  rwa [h.joined_fp_e1] at hr

theorem reach_e2_f1 (h : IsPinch S δ) : reachSide h.splitMap h.e2 h.f1 := by
  have hr := PinchLemma.eqvGen_facePerm (M := h.splitMap) h.e2
  rwa [h.joined_fp_e2] at hr

/-! ### The exterior cycle -/

theorem far_cyc (h : IsPinch S δ) : ∀ x ∈ S.cyc, x ≠ δ ∧ x ≠ S.map.alpha δ :=
  fun _ hx => ⟨fun he => h.not_mem (he ▸ hx), fun he => h.not_mem_alpha (he ▸ hx)⟩

theorem next_cyc (h : IsPinch S δ) {x : S.map.Dart} (hx : x ∈ S.cyc) :
    EdgeDeletion.next S.map δ x = S.map.facePerm x :=
  have hm := h.far_cyc _ ((isFaceCycle_facePerm_mem_iff S.isFaceCycle x).mpr hx)
  EdgeDeletion.next_of_ne_of_ne S.map δ hm.1 hm.2

/-- The exterior cycle, read in the deleted map. -/
noncomputable def delCyc (h : IsPinch S δ) : List (S.delMap δ).Dart :=
  (EdgeDeletion.exists_map_value_eq S.map δ S.cyc h.far_cyc).choose

theorem map_value_delCyc (h : IsPinch S δ) :
    h.delCyc.map (EdgeDeletion.value S.map δ) = S.cyc :=
  (EdgeDeletion.exists_map_value_eq S.map δ S.cyc h.far_cyc).choose_spec

theorem mem_delCyc_iff (h : IsPinch S δ) (x : (S.delMap δ).Dart) :
    x ∈ h.delCyc ↔ EdgeDeletion.value S.map δ x ∈ S.cyc := by
  have hm : EdgeDeletion.value S.map δ x ∈ h.delCyc.map (EdgeDeletion.value S.map δ) ↔
      x ∈ h.delCyc :=
    List.mem_map_of_injective (EdgeDeletion.value_injective S.map δ)
  rw [h.map_value_delCyc] at hm
  exact hm.symm

theorem del_isFaceCycle (h : IsPinch S δ) : (S.delMap δ).IsFaceCycle h.delCyc :=
  EdgeDeletion.isFaceCycle_of_map_value S.map δ h.map_value_delCyc S.isFaceCycle.ne_nil
    S.isFaceCycle.nodup
    (S.isFaceCycle.chain.imp_of_mem_imp fun _ _ ha _ hab => (h.next_cyc ha).trans hab)
    (fun u hu v hv => by
      obtain rfl : S.cyc.getLast S.isFaceCycle.ne_nil = u :=
        Option.some.inj ((List.getLast?_eq_some_getLast S.isFaceCycle.ne_nil).symm.trans hu)
      obtain rfl : S.cyc.head S.isFaceCycle.ne_nil = v :=
        Option.some.inj ((List.head?_eq_some_head S.isFaceCycle.ne_nil).symm.trans hv)
      exact (h.next_cyc (List.getLast_mem S.isFaceCycle.ne_nil)).trans S.isFaceCycle.closes)

theorem joined_isFaceCycle (h : IsPinch S δ) : h.splitMap.IsFaceCycle h.delCyc :=
  FoldMap.joined_isFaceCycle_of_avoid h.del_isFaceCycle
    (fun hm : h.e1 ∈ h.delCyc => h.e1_not_mem ((h.mem_delCyc_iff _).mp hm))
    (fun hm : h.f1 ∈ h.delCyc => h.f1_not_mem ((h.mem_delCyc_iff _).mp hm))

/-! ### The split stage -/

theorem splitMap_lab_sigma (h : IsPinch S δ) (z : h.splitMap.Dart) :
    S.lab (EdgeDeletion.value S.map δ (h.splitMap.sigma z)) =
      S.lab (EdgeDeletion.value S.map δ z) := by
  have hv : S.lab (EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.e1)) =
      S.lab (EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.f1)) := by
    rw [show EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.e1) =
        S.map.alpha (S.map.facePerm δ) from EdgeDeletion.alpha_val S.map δ h.e1,
      show EdgeDeletion.value S.map δ ((S.delMap δ).alpha h.f1) =
        S.map.alpha (S.map.facePerm (S.map.alpha δ)) from EdgeDeletion.alpha_val S.map δ h.f1,
      ← S.lab_facePerm, ← S.lab_facePerm]
    exact OrbitClassifier.eq_of_sameCycle S.map.sigma S.lab S.lab_sigma h.pinch
  show S.lab (EdgeDeletion.value S.map δ ((S.delMap δ).sigma
    (Equiv.swap ((S.delMap δ).alpha h.e1) ((S.delMap δ).alpha h.f1) z))) = _
  rw [deletion_lab_sigma S δ]
  exact Equiv.apply_swap_eq_self
    (v := fun w : (S.delMap δ).Dart => S.lab (EdgeDeletion.value S.map δ w)) hv z

theorem splitMap_bad_facePerm (h : IsPinch S δ) (z : h.splitMap.Dart) :
    (h.splitMap.facePerm z = h.e1 ∨ h.splitMap.facePerm z = h.e2 ∨
      h.splitMap.facePerm z = h.f1 ∨ h.splitMap.facePerm z = h.f2) ↔
      (z = h.e1 ∨ z = h.e2 ∨ z = h.f1 ∨ z = h.f2) := by
  have hinj := h.splitMap.facePerm.injective
  constructor
  · rintro (hz | hz | hz | hz)
    · exact Or.inr (Or.inr (Or.inr (hinj (hz.trans h.joined_fp_f2.symm))))
    · exact Or.inr (Or.inr (Or.inl (hinj (hz.trans h.joined_fp_f1.symm))))
    · exact Or.inr (Or.inl (hinj (hz.trans h.joined_fp_e2.symm)))
    · exact Or.inl (hinj (hz.trans h.joined_fp_e1.symm))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inr h.joined_fp_e1))
    · exact Or.inr (Or.inr (Or.inl h.joined_fp_e2))
    · exact Or.inr (Or.inl h.joined_fp_f1)
    · exact Or.inl h.joined_fp_f2

theorem delCyc_not_bad (h : IsPinch S δ) (z : (S.delMap δ).Dart) (hz : z ∈ h.delCyc) :
    ¬ (z = h.e1 ∨ z = h.e2 ∨ z = h.f1 ∨ z = h.f2) := by
  have hm := (h.mem_delCyc_iff z).mp hz
  rintro (rfl | rfl | rfl | rfl)
  · exact h.e1_not_mem hm
  · exact h.e2_not_mem hm
  · exact h.f1_not_mem hm
  · exact h.f2_not_mem hm

/-- Off the square, face rotation of the split map is face rotation of the stage. -/
theorem splitMap_comm (h : IsPinch S δ) (x : h.splitMap.Dart)
    (hxb : ¬ (x = h.e1 ∨ x = h.e2 ∨ x = h.f1 ∨ x = h.f2)) :
    EdgeDeletion.value S.map δ (h.splitMap.facePerm x) =
      S.map.facePerm (EdgeDeletion.value S.map δ x) := by
  have h1 : x ≠ h.e1 := fun he => hxb (Or.inl he)
  have h2 : x ≠ h.e2 := fun he => hxb (Or.inr (Or.inl he))
  have h3 : x ≠ h.f1 := fun he => hxb (Or.inr (Or.inr (Or.inl he)))
  have h4 : x ≠ h.f2 := fun he => hxb (Or.inr (Or.inr (Or.inr he)))
  rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne h1 h3,
    EdgeDeletion.value_facePerm_eq_next]
  refine EdgeDeletion.next_of_ne_of_ne S.map δ (fun hx => h2 ?_) (fun hx => h4 ?_)
  · exact EdgeDeletion.value_injective S.map δ (S.map.facePerm.injective (hx.trans h.back.symm))
  · exact EdgeDeletion.value_injective S.map δ
      (S.map.facePerm.injective (hx.trans h.back_alpha.symm))

/-- **The split stage**: the split map, pending the square `e1, e2, f1, f2`. -/
noncomputable def pinchStage (h : IsPinch S δ) : FoldStage X where
  map := h.splitMap
  lab := fun z => S.lab (EdgeDeletion.value S.map δ z)
  lab_sigma := h.splitMap_lab_sigma
  adj := fun z => deletion_adj S δ z
  cyc := h.delCyc
  isFaceCycle := h.joined_isFaceCycle
  bad := fun z => z = h.e1 ∨ z = h.e2 ∨ z = h.f1 ∨ z = h.f2
  bad_facePerm := h.splitMap_bad_facePerm
  cyc_bad := h.delCyc_not_bad
  tri := fun x hx hxb =>
    tri_of_embed S (N := h.splitMap) (fun z => S.lab (EdgeDeletion.value S.map δ z))
      h.joined_isFaceCycle (fun z => z = h.e1 ∨ z = h.e2 ∨ z = h.f1 ∨ z = h.f2)
      h.splitMap_bad_facePerm (EdgeDeletion.value S.map δ) (EdgeDeletion.value_injective S.map δ)
      (fun _ => rfl) (fun y hy hm => hy ((h.mem_delCyc_iff y).mpr hm)) (fun _ _ => h.good _)
      (fun y _ hyb => h.splitMap_comm y hyb) x hx hxb

theorem pinchStage_boundary (h : IsPinch S δ) : h.pinchStage.boundary = S.boundary :=
  boundary_eq_of_map_lab (by
    show h.delCyc.map (fun z => S.lab (EdgeDeletion.value S.map δ z)) = S.cyc.map S.lab
    have hm := congrArg (List.map S.lab) h.map_value_delCyc
    rwa [List.map_map] at hm)

theorem pinchStage_faceCount (h : IsPinch S δ) :
    h.pinchStage.map.faceCount = S.map.faceCount :=
  h.joined_faceCount

end IsPinch

/-- **The pinched fold.**  A pinch configuration in a stage with boundary `γ` gives a
triangulated disc with boundary `γ` and at least three faces fewer. -/
theorem exists_disc_of_pinch {S : FoldStage X} {δ : S.map.Dart} (h : IsPinch S δ)
    {γ : List V} (hb : S.boundary = γ) :
    ∃ D : TriangulatedDisc X γ, D.innerFaceCount + 3 ≤ S.map.faceCount := by
  have hb' : h.pinchStage.boundary = γ := h.pinchStage_boundary.trans hb
  have hf : h.pinchStage.map.faceCount = S.map.faceCount := h.pinchStage_faceCount
  rcases h.reach (h.delCyc.head h.joined_isFaceCycle.ne_nil) with hr | hr
  · obtain ⟨D, hD⟩ := exists_disc_of_sides h.pinchStage h.e2 h.joined_euler (c' := h.e1)
      h.reach h.not_reach (reachSide_of_head h.pinchStage hr) (Or.inr (Or.inl rfl))
      ((congrArg h.splitMap.facePerm h.joined_fp_e2).trans h.joined_fp_f1)
      (fun z hz => by
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr h.not_reach)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h.joined_fp_e2.symm)
        · exact Or.inr (Or.inr fun hr2 => h.not_reach
            (Relation.EqvGen.trans _ _ _ hr2 (Relation.EqvGen.symm _ _ h.reach_e1_f2))))
      hb'
    exact ⟨D, by omega⟩
  · have hcc' : ¬ reachSide h.splitMap h.e1 h.e2 := fun hr2 =>
      h.not_reach (Relation.EqvGen.symm _ _ hr2)
    obtain ⟨D, hD⟩ := exists_disc_of_sides h.pinchStage h.e1 h.joined_euler (c' := h.e2)
      (fun x => (h.reach x).symm) hcc' (reachSide_of_head h.pinchStage hr) (Or.inl rfl)
      ((congrArg h.splitMap.facePerm h.joined_fp_e1).trans h.joined_fp_f2)
      (fun z hz => by
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hcc')
        · exact Or.inr (Or.inr fun hr2 => h.not_reach
            (Relation.EqvGen.trans _ _ _ h.reach_e2_f1 (Relation.EqvGen.symm _ _ hr2)))
        · exact Or.inr (Or.inl h.joined_fp_e1.symm))
      hb'
    exact ⟨D, by omega⟩

end FoldStage

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.FoldStage.IsPinch.del_pinch
#audit_axioms GroupApproximation.Systolic.FoldStage.IsPinch.joined_euler
#audit_axioms GroupApproximation.Systolic.FoldStage.IsPinch.pinchStage_boundary
#audit_axioms GroupApproximation.Systolic.FoldStage.IsPinch.pinchStage_faceCount
#audit_axioms GroupApproximation.Systolic.FoldStage.exists_disc_of_pinch
