import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinched two-gon pocket is a pocket region

A model test for `PocketRegion` (`Estimating/OsinPocketRegion.lean`), the subdiagram `Γ_1` of
Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b), on the map of
`Estimating/OsinPocketPinchedTwoGonModel.lean`.  There the digons `a = [3,4]` and `b = [5,6]`
meet only at the vertex `{1,3,6,8}`, and `no_faceSetBoundary` shows that the face set `{a, b}`
has no embedded face-set boundary.

The face set `{a, b}` is still a pocket region (`pocket`):

* the cycle `[5,3,4,6]` lists its four boundary darts.  Reclosing along it splits the pinch vertex
  into `{1,3}` and `{6,8}`, so the reclosed map has 4 vertices, 5 edges and 3 faces
  (`innerRegion`);
* the complement `{Π, exterior}` has one internal edge `{2,7}`, and its cycle `[9,8,0,1]` lists the
  other sides of the same four edges.  Reclosing gives 3 vertices, 4 edges and 3 faces
  (`outerRegion`);
* the reverse of the complement's cycle, mapped by edge reversal, is the cycle of the pocket.

Euler preservation is counted by hand.  The cycle of the pocket does not follow the face-set
boundary (`not_followsBoundary`), so the first-return vertex count of
`SurgeryReclosedVertices.lean` does not apply to it.  The cycle also passes twice through the pinch
vertex (`not_isSimpleClosedWalk`).  So `PocketRegion` admits pinched pockets, and a producer that
reads a simple closed walk or a genuine boundary walk off a pocket region needs a hypothesis that
excludes the pinch.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a) and (b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

open Equiv
open Surgery.MapCollapse (InternalDart IsBoundaryDart KeptDart BoundaryCycle IsDiscRegion
  reclosedMap reclosedMap_facePerm_val_of_mem reclosedMap_facePerm_val_of_notMem
  reclosedMap_faceCount reclosedMap_connected)

/-- A permutation of a subtype that agrees with a permutation of the ambient type moves points
along the same cycles. -/
theorem sameCycle_of_val {α : Type*} {P : α → Prop} [Finite α] (p : Perm {x // P x})
    (q : Perm α) (hpq : ∀ d, (p d).1 = q d.1) (d e : {x // P x})
    (h : q.SameCycle d.1 e.1) : p.SameCycle d e := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ k : ℕ, ((p ^ k) d).1 = (q ^ k) d.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, hpq, ih]
  exact ⟨n, by rw [zpow_natCast]; exact Subtype.ext ((hpow n).trans hn)⟩

/-! ## The pocket -/

theorem mem_pinchFaces_iff (x : Fin 10) :
    diagram.toCombMap.faceOf x ∈ pinchFaces ↔ faceClass x = 1 ∨ faceClass x = 2 :=
  Finset.mem_cons.trans (or_congr (faceOf_eq_face x 1)
    (Finset.mem_singleton.trans (faceOf_eq_face x 2)))

theorem innerBoundaryDart_iff (d : Fin 10) :
    IsBoundaryDart diagram.toCombMap pinchFaces d ↔ d ∈ ([5, 3, 4, 6] : List (Fin 10)) := by
  change (M.faceOf d ∈ Finset.cons (face 1) {face 2} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 1) {face 2} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem not_internalDart_pinch (d : Fin 10) : ¬ InternalDart diagram.toCombMap pinchFaces d := by
  rintro ⟨hd, hα⟩
  change M.faceOf d ∈ Finset.cons (face 1) {face 2} _ at hd
  change M.faceOf (M.alpha d) ∈ Finset.cons (face 1) {face 2} _ at hα
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face] at hd hα
  revert hd hα
  fin_cases d <;> decide

/-- The four boundary darts of the pocket, in the order of the new face. -/
def innerCycle : BoundaryCycle diagram.toCombMap pinchFaces where
  cycle := ([5, 3, 4, 6] : List (Fin 10))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([5, 3, 4, 6] : List (Fin 10)).Nodup)
  cycle_mem_iff := fun d => (innerBoundaryDart_iff d).symm

/-- The face rotation of the reclosed pocket, on the ambient darts. -/
def innerRot : Fin 10 → Fin 10 := ![1, 2, 0, 4, 6, 3, 5, 9, 7, 8]

/-- The vertex rotation of the reclosed pocket, on the ambient darts. -/
def innerVertexRot : Perm (Fin 10) where
  toFun := ![4, 3, 9, 1, 7, 2, 8, 0, 6, 5]
  invFun := ![7, 3, 5, 1, 0, 9, 8, 4, 6, 2]
  left_inv := by decide
  right_inv := by decide

theorem innerCycle_next :
    ∀ (x : Fin 10) (hx : x ∈ ([5, 3, 4, 6] : List (Fin 10))),
      List.next [5, 3, 4, 6] x hx = innerRot x := by
  decide

theorem innerRot_of_not_mem :
    ∀ x : Fin 10, ¬(faceClass x = 1 ∨ faceClass x = 2) → M.facePerm x = innerRot x := by
  decide

theorem innerRot_alpha : ∀ x : Fin 10, innerRot (M.alpha x) = innerVertexRot x := by
  decide

theorem innerRot_val (e : KeptDart diagram.toCombMap pinchFaces) :
    ((reclosedMap diagram.toCombMap pinchFaces innerCycle).facePerm e).1 = innerRot e.1 := by
  obtain ⟨x, hx⟩ := e
  by_cases h : diagram.toCombMap.faceOf x ∈ pinchFaces
  · rw [reclosedMap_facePerm_val_of_mem diagram.toCombMap pinchFaces innerCycle ⟨x, hx⟩ h,
      Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val]
    exact innerCycle_next x _
  · rw [reclosedMap_facePerm_val_of_notMem diagram.toCombMap pinchFaces innerCycle ⟨x, hx⟩ h]
    exact innerRot_of_not_mem x ((mem_pinchFaces_iff x).not.mp h)

theorem innerVertexRot_val (d : KeptDart diagram.toCombMap pinchFaces) :
    ((reclosedMap diagram.toCombMap pinchFaces innerCycle).sigma d).1 = innerVertexRot d.1 := by
  have hs : (reclosedMap diagram.toCombMap pinchFaces innerCycle).facePerm
      ((reclosedMap diagram.toCombMap pinchFaces innerCycle).alpha d) =
      (reclosedMap diagram.toCombMap pinchFaces innerCycle).sigma d := by
    change (reclosedMap diagram.toCombMap pinchFaces innerCycle).sigma
      ((reclosedMap diagram.toCombMap pinchFaces innerCycle).alpha
        ((reclosedMap diagram.toCombMap pinchFaces innerCycle).alpha d)) = _
    rw [(reclosedMap diagram.toCombMap pinchFaces innerCycle).alpha_involutive]
  rw [← hs, innerRot_val]
  exact innerRot_alpha d.1

def innerVertexClass : Fin 10 → Fin 4 := ![0, 1, 2, 1, 0, 2, 3, 0, 3, 2]
def innerVertexRep : Fin 4 → Fin 10 := ![0, 1, 2, 6]

theorem innerVertexClass_rot :
    ∀ x : Fin 10, innerVertexClass (innerVertexRot x) = innerVertexClass x := by
  decide

theorem innerVertexClass_rep : ∀ i : Fin 4, innerVertexClass (innerVertexRep i) = i := by
  decide

theorem innerVertexRot_sameCycle :
    ∀ x : Fin 10, innerVertexRot.SameCycle (innerVertexRep (innerVertexClass x)) x := by
  decide

/-- The vertices of the reclosed pocket: the pinch vertex splits into `{1,3}` and `{6,8}`. -/
noncomputable def innerVertexEquiv :
    (reclosedMap diagram.toCombMap pinchFaces innerCycle).Vertex ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv (reclosedMap diagram.toCombMap pinchFaces innerCycle).sigma
    (fun d : KeptDart diagram.toCombMap pinchFaces => innerVertexClass d.1)
    (fun i => (⟨innerVertexRep i, not_internalDart_pinch _⟩ :
      KeptDart diagram.toCombMap pinchFaces))
    (fun d => (congrArg innerVertexClass (innerVertexRot_val d)).trans
      (innerVertexClass_rot d.1))
    (fun i => innerVertexClass_rep i)
    (fun d => sameCycle_of_val (reclosedMap diagram.toCombMap pinchFaces innerCycle).sigma
      innerVertexRot innerVertexRot_val
      ⟨innerVertexRep (innerVertexClass d.1), not_internalDart_pinch _⟩ d
      (innerVertexRot_sameCycle d.1))

theorem innerMap_vertexCount :
    (reclosedMap diagram.toCombMap pinchFaces innerCycle).vertexCount = 4 :=
  (Nat.card_congr innerVertexEquiv).trans (by simp)

theorem innerMap_dartCount :
    (reclosedMap diagram.toCombMap pinchFaces innerCycle).dartCount = 10 :=
  (Nat.card_congr (Equiv.subtypeUnivEquiv not_internalDart_pinch)).trans (by simp)

theorem pinchFaces_card : pinchFaces.card = 1 + 1 :=
  (Finset.card_cons _).trans (congrArg (· + 1) (Finset.card_singleton _))

theorem innerMap_euler :
    (reclosedMap diagram.toCombMap pinchFaces innerCycle).eulerCharacteristic =
      diagram.toCombMap.eulerCharacteristic := by
  have hE := (reclosedMap diagram.toCombMap pinchFaces innerCycle).dartCount_eq_two_mul_edgeCount
  rw [innerMap_dartCount] at hE
  have hF := reclosedMap_faceCount diagram.toCombMap pinchFaces innerCycle
  have hF0 : diagram.toCombMap.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
  rw [pinchFaces_card, hF0] at hF
  have hE5 : (reclosedMap diagram.toCombMap pinchFaces innerCycle).edgeCount = 5 := by omega
  have hF3 : (reclosedMap diagram.toCombMap pinchFaces innerCycle).faceCount = 3 := by omega
  have h2 : diagram.toCombMap.eulerCharacteristic = 2 := diagram.planar.2
  rw [h2]
  unfold CombMap.eulerCharacteristic
  rw [innerMap_vertexCount, hE5, hF3]
  norm_num

/-- **The pocket is a disc region.** -/
noncomputable def innerRegion : IsDiscRegion diagram.toCombMap pinchFaces where
  toBoundaryCycle := innerCycle
  reclosed_connected := reclosedMap_connected _ _ innerCycle diagram.planar.1
  euler_preserved := innerMap_euler

/-! ## The complement -/

/-- The relator cell and the exterior face. -/
def outsideFaces : Finset diagram.toCombMap.Face :=
  Finset.cons (face 0) {face 3} fun h =>
    absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

theorem mem_outsideFaces_iff (x : Fin 10) :
    diagram.toCombMap.faceOf x ∈ outsideFaces ↔ faceClass x = 0 ∨ faceClass x = 3 :=
  Finset.mem_cons.trans (or_congr (faceOf_eq_face x 0)
    (Finset.mem_singleton.trans (faceOf_eq_face x 3)))

theorem outsideBoundaryDart_iff (d : Fin 10) :
    IsBoundaryDart diagram.toCombMap outsideFaces d ↔ d ∈ ([9, 8, 0, 1] : List (Fin 10)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem internalDart_outside_iff (d : Fin 10) :
    InternalDart diagram.toCombMap outsideFaces d ↔ d = 2 ∨ d = 7 := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∈ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The boundary darts of the complement: the other sides of the four edges of the pocket. -/
def outerCycle : BoundaryCycle diagram.toCombMap outsideFaces where
  cycle := ([9, 8, 0, 1] : List (Fin 10))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([9, 8, 0, 1] : List (Fin 10)).Nodup)
  cycle_mem_iff := fun d => (outsideBoundaryDart_iff d).symm

/-- The face rotation of the reclosed complement, on the ambient darts (`2` and `7` are
deleted). -/
def outerRot : Fin 10 → Fin 10 := ![1, 9, 2, 4, 3, 6, 5, 7, 0, 8]

/-- The vertex rotation of the reclosed complement, on the ambient darts. -/
def outerVertexRot : Perm (Fin 10) where
  toFun := ![4, 6, 7, 1, 0, 9, 8, 2, 3, 5]
  invFun := ![4, 3, 7, 8, 0, 9, 1, 2, 6, 5]
  left_inv := by decide
  right_inv := by decide

theorem outerCycle_next :
    ∀ (x : Fin 10) (hx : x ∈ ([9, 8, 0, 1] : List (Fin 10))),
      List.next [9, 8, 0, 1] x hx = outerRot x := by
  decide

theorem outerRot_of_not_mem :
    ∀ x : Fin 10, ¬(faceClass x = 0 ∨ faceClass x = 3) → M.facePerm x = outerRot x := by
  decide

theorem outerRot_alpha : ∀ x : Fin 10, outerRot (M.alpha x) = outerVertexRot x := by
  decide

theorem outerRot_val (e : KeptDart diagram.toCombMap outsideFaces) :
    ((reclosedMap diagram.toCombMap outsideFaces outerCycle).facePerm e).1 = outerRot e.1 := by
  obtain ⟨x, hx⟩ := e
  by_cases h : diagram.toCombMap.faceOf x ∈ outsideFaces
  · rw [reclosedMap_facePerm_val_of_mem diagram.toCombMap outsideFaces outerCycle ⟨x, hx⟩ h,
      Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val]
    exact outerCycle_next x _
  · rw [reclosedMap_facePerm_val_of_notMem diagram.toCombMap outsideFaces outerCycle ⟨x, hx⟩ h]
    exact outerRot_of_not_mem x ((mem_outsideFaces_iff x).not.mp h)

theorem outerVertexRot_val (d : KeptDart diagram.toCombMap outsideFaces) :
    ((reclosedMap diagram.toCombMap outsideFaces outerCycle).sigma d).1 = outerVertexRot d.1 := by
  have hs : (reclosedMap diagram.toCombMap outsideFaces outerCycle).facePerm
      ((reclosedMap diagram.toCombMap outsideFaces outerCycle).alpha d) =
      (reclosedMap diagram.toCombMap outsideFaces outerCycle).sigma d := by
    change (reclosedMap diagram.toCombMap outsideFaces outerCycle).sigma
      ((reclosedMap diagram.toCombMap outsideFaces outerCycle).alpha
        ((reclosedMap diagram.toCombMap outsideFaces outerCycle).alpha d)) = _
    rw [(reclosedMap diagram.toCombMap outsideFaces outerCycle).alpha_involutive]
  rw [← hs, outerRot_val]
  exact outerRot_alpha d.1

def outerVertexClass : Fin 10 → Fin 3 := ![0, 1, 0, 1, 0, 2, 1, 0, 1, 2]
def outerVertexRep : Fin 3 → Fin 10 := ![0, 1, 5]

theorem outerVertexClass_rot :
    ∀ x : Fin 10, outerVertexClass (outerVertexRot x) = outerVertexClass x := by
  decide

theorem outerVertexClass_rep : ∀ i : Fin 3, outerVertexClass (outerVertexRep i) = i := by
  decide

theorem outerVertexRot_sameCycle : ∀ x : Fin 10, x ≠ 2 → x ≠ 7 →
    outerVertexRot.SameCycle (outerVertexRep (outerVertexClass x)) x := by
  decide

theorem outerVertexRep_kept (i : Fin 3) :
    ¬ InternalDart diagram.toCombMap outsideFaces (outerVertexRep i) := by
  rw [internalDart_outside_iff]
  fin_cases i <;> decide

theorem ne_two_of_kept (d : KeptDart diagram.toCombMap outsideFaces) : (d.1 : Fin 10) ≠ 2 :=
  fun h => d.2 ((internalDart_outside_iff d.1).mpr (Or.inl h))

theorem ne_seven_of_kept (d : KeptDart diagram.toCombMap outsideFaces) : (d.1 : Fin 10) ≠ 7 :=
  fun h => d.2 ((internalDart_outside_iff d.1).mpr (Or.inr h))

/-- The vertices of the reclosed complement. -/
noncomputable def outerVertexEquiv :
    (reclosedMap diagram.toCombMap outsideFaces outerCycle).Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv (reclosedMap diagram.toCombMap outsideFaces outerCycle).sigma
    (fun d : KeptDart diagram.toCombMap outsideFaces => outerVertexClass d.1)
    (fun i => (⟨outerVertexRep i, outerVertexRep_kept i⟩ :
      KeptDart diagram.toCombMap outsideFaces))
    (fun d => (congrArg outerVertexClass (outerVertexRot_val d)).trans
      (outerVertexClass_rot d.1))
    (fun i => outerVertexClass_rep i)
    (fun d => sameCycle_of_val (reclosedMap diagram.toCombMap outsideFaces outerCycle).sigma
      outerVertexRot outerVertexRot_val
      ⟨outerVertexRep (outerVertexClass d.1), outerVertexRep_kept _⟩ d
      (outerVertexRot_sameCycle d.1 (ne_two_of_kept d) (ne_seven_of_kept d)))

theorem outerMap_vertexCount :
    (reclosedMap diagram.toCombMap outsideFaces outerCycle).vertexCount = 3 :=
  (Nat.card_congr outerVertexEquiv).trans (by simp)

theorem outerMap_dartCount :
    (reclosedMap diagram.toCombMap outsideFaces outerCycle).dartCount = 8 := by
  let e : KeptDart diagram.toCombMap outsideFaces ≃ {d : Fin 10 // ¬(d = 2 ∨ d = 7)} :=
    Equiv.subtypeEquivRight fun d => not_congr (internalDart_outside_iff d)
  have h := Nat.card_congr e
  change Nat.card (KeptDart diagram.toCombMap outsideFaces) = 8
  rw [h, Nat.card_eq_fintype_card]
  decide

theorem outsideFaces_card : outsideFaces.card = 1 + 1 :=
  (Finset.card_cons _).trans (congrArg (· + 1) (Finset.card_singleton _))

theorem outerMap_euler :
    (reclosedMap diagram.toCombMap outsideFaces outerCycle).eulerCharacteristic =
      diagram.toCombMap.eulerCharacteristic := by
  have hE := (reclosedMap diagram.toCombMap outsideFaces outerCycle).dartCount_eq_two_mul_edgeCount
  rw [outerMap_dartCount] at hE
  have hF := reclosedMap_faceCount diagram.toCombMap outsideFaces outerCycle
  have hF0 : diagram.toCombMap.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
  rw [outsideFaces_card, hF0] at hF
  have hE4 : (reclosedMap diagram.toCombMap outsideFaces outerCycle).edgeCount = 4 := by omega
  have hF3 : (reclosedMap diagram.toCombMap outsideFaces outerCycle).faceCount = 3 := by omega
  have h2 : diagram.toCombMap.eulerCharacteristic = 2 := diagram.planar.2
  rw [h2]
  unfold CombMap.eulerCharacteristic
  rw [outerMap_vertexCount, hE4, hF3]
  norm_num

/-- **The complement is a disc region.** -/
noncomputable def outerRegion : IsDiscRegion diagram.toCombMap outsideFaces where
  toBoundaryCycle := outerCycle
  reclosed_connected := reclosedMap_connected _ _ outerCycle diagram.planar.1
  euler_preserved := outerMap_euler

theorem mem_outsideFaces_iff_not_mem (f : diagram.toCombMap.Face) :
    f ∈ outsideFaces ↔ f ∉ pinchFaces := by
  obtain ⟨i, rfl⟩ : ∃ i, face i = f :=
    ⟨faceEquiv f, faceEquiv.injective (faceEquiv_face (faceEquiv f))⟩
  change face i ∈ Finset.cons (face 0) {face 3} _ ↔ ¬ face i ∈ Finset.cons (face 1) {face 2} _
  simp only [Finset.mem_cons, Finset.mem_singleton, face_eq_iff]
  fin_cases i <;> decide

/-! ## The pocket region -/

/-- **The pinched pocket is a pocket region.** -/
noncomputable def pocket : PocketRegion diagram where
  faces := pinchFaces
  outside := outsideFaces
  mem_outside_iff := mem_outsideFaces_iff_not_mem
  outerFace_mem := Finset.mem_cons.mpr (Or.inr (Finset.mem_singleton_self _))
  inner := innerRegion
  outer := outerRegion
  invDarts_outer_rotate := ⟨0, by decide⟩

theorem pocket_faces : pocket.faces = pinchFaces := rfl

theorem pocket_inner_cycle : pocket.inner.cycle = ([5, 3, 4, 6] : List (Fin 10)) := rfl

theorem innerCycle_next_five_ne :
    ∀ hx : (5 : Fin 10) ∈ ([5, 3, 4, 6] : List (Fin 10)),
      List.next [5, 3, 4, 6] 5 hx ≠ M.facePerm 5 := by
  decide

/-- **The cycle of the pocket does not follow the face-set boundary.**  After the dart `5` the
cycle goes to `3`, across the pinch vertex, while the face `b` goes on to `6`, and no dart of the
pocket is internal. -/
theorem not_followsBoundary : ¬ pocket.inner.toBoundaryCycle.FollowsBoundary := by
  intro h
  have hw := h ⟨5, (innerBoundaryDart_iff 5).mpr (by decide)⟩
  rw [Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val] at hw
  rcases Relation.ReflTransGen.cases_tail hw with heq | ⟨c, -, hc, -⟩
  · exact innerCycle_next_five_ne _ heq
  · exact not_internalDart_pinch c hc

/-- **The cycle of the pocket is not a simple closed walk:** the darts `3` and `6` start at the
pinch vertex. -/
theorem not_isSimpleClosedWalk : ¬ IsSimpleClosedWalk diagram.toCombMap pocket.inner.cycle := by
  intro h
  have hv : diagram.toCombMap.vertexOf (3 : Fin 10) = diagram.toCombMap.vertexOf (6 : Fin 10) :=
    vertexEquiv.injective (by decide)
  have hnodup := h.vertex_nodup
  change [diagram.toCombMap.vertexOf (5 : Fin 10), diagram.toCombMap.vertexOf (3 : Fin 10),
    diagram.toCombMap.vertexOf (4 : Fin 10), diagram.toCombMap.vertexOf (6 : Fin 10)].Nodup
    at hnodup
  rw [hv] at hnodup
  exact (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 (by simp)

#audit_axioms sameCycle_of_val
#audit_closed_axioms innerMap_euler
#audit_closed_axioms outerMap_euler
#audit_axioms pocket
#audit_axioms not_followsBoundary
#audit_axioms not_isSimpleClosedWalk

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
