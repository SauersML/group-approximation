import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPosModelsAlgebra
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapRose
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagram of the ε = 1 counterexample to the positive pinch

The disc diagram and the pocket face set of the counterexample to `PocketPinchLabelledPosStatement`
at `ε = 1`, over the group of `OsinPocketPinchPosModelsAlgebra`: the free group on `a, b, d, e, x, y`
with the relator words `P = a a b` and `Q = d d e` and the boundary letter `c = x P x⁻¹ y Q y⁻¹`.

The map has twenty darts; darts `2k` and `2k + 1` are the two ends of edge `k`:
* the loop `c` at the vertex `O` (darts `0, 1`);
* the edges `e_1`, `e_2` from `O` to `v`, both reading `x` (darts `2, 3` and `4, 5`);
* the bridge from `O` to `u` reading `y` (darts `6, 7`);
* the triangle `Π` at `v`, reading `a, a, b` through `p_1`, `p_2` (darts `8`–`13`);
* the triangle `R` at `u`, reading `d, d, e` through `r_1`, `r_2` (darts `14`–`19`).

Its faces are the `G`-cell `κ = [0,6,19,17,15,7,4,13,11,9,3]` reading `c · y Q⁻¹ y⁻¹ · x P⁻¹ x⁻¹`,
the relator cells `Π = [8,10,12]` and `R = [14,16,18]`, the exterior face `[1]` reading `c⁻¹`, and
the `G`-digon `[2,5]` reading `x x⁻¹`.  The labels are letters of the base set.

* `pinchK`: the face set `{κ, R}` is a pocket face set at `ε = 1` between the positions `0` and
  `1`, with source `Π`, kept cell `R`, the sides `[4]` (`x`) and `[3]` (`x⁻¹`), all of `∂Π` read
  backwards as `t_1`, and all of `∂X` as `t_2`.
* `pinchK_closedWalk`: its cycle `[4,13,11,9,3,0]` is in walk order.  It passes `v` twice, so it is
  not simple.

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels

open GGT Equiv
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

def pinchAlpha : Perm (Fin 20) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18]
  left_inv := by decide
  right_inv := by decide

/-- The rotations `0 ↦ 1 ↦ 6 ↦ 4 ↦ 2 ↦ 0` at `O`, `5 ↦ 13 ↦ 8 ↦ 3 ↦ 5` at `v`, `7 ↦ 19 ↦ 14 ↦ 7`
at `u`, and the two-dart rotations at `p_1`, `p_2`, `r_1`, `r_2`. -/
def pinchSigma : Perm (Fin 20) where
  toFun := ![1, 6, 0, 5, 2, 13, 4, 19, 3, 10, 9, 12, 11, 8, 7, 16, 15, 18, 17, 14]
  invFun := ![2, 0, 4, 8, 6, 3, 1, 14, 13, 10, 9, 12, 11, 5, 19, 16, 15, 18, 17, 7]
  left_inv := by decide
  right_inv := by decide

/-- The map of the counterexample. -/
def M : CombMap where
  Dart := Fin 20
  dartFintype := inferInstance
  alpha := pinchAlpha
  sigma := pinchSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 20))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 20) n)

/-- The faces `κ`, `Π`, the exterior, `R` and the digon are the classes `0, 1, 2, 3, 4`. -/
def faceClass : Fin 20 → Fin 5 := ![0, 2, 4, 0, 0, 4, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0]
def faceRep : Fin 5 → Fin 20 := ![0, 8, 1, 14, 2]

noncomputable def faceEquiv : M.Face ≃ Fin 5 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

def face (i : Fin 5) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 5) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 20) (i : Fin 5) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 5) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

/-- The vertices `O, v, p_1, p_2, u, r_1, r_2` are the classes `0, …, 6`. -/
def vertexClass : Fin 20 → Fin 7 := ![0, 0, 0, 1, 0, 1, 0, 4, 1, 2, 2, 3, 3, 1, 4, 5, 5, 6, 6, 4]
def vertexRep : Fin 7 → Fin 20 := ![0, 3, 9, 11, 7, 15, 17]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep (by decide) (by decide) (by decide)

theorem vertexOf_eq_of_class {d e : Fin 20} (h : vertexClass d = vertexClass e) :
    M.vertexOf d = M.vertexOf e := by
  apply vertexEquiv.injective
  exact h

theorem planar : M.IsPlanar := by
  constructor
  · have trans {d e f : M.Dart} (hde : Relation.EqvGen M.Adjacent d e)
        (hef : Relation.EqvGen M.Adjacent e f) : Relation.EqvGen M.Adjacent d f :=
      .trans _ _ _ hde hef
    have h1 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
    have h6 : Relation.EqvGen M.Adjacent 0 6 := trans h1 (.rel _ _ (Or.inr rfl))
    have h4 : Relation.EqvGen M.Adjacent 0 4 := trans h6 (.rel _ _ (Or.inr rfl))
    have h2 : Relation.EqvGen M.Adjacent 0 2 := trans h4 (.rel _ _ (Or.inr rfl))
    have h3 : Relation.EqvGen M.Adjacent 0 3 := trans h2 (.rel _ _ (Or.inl rfl))
    have h5 : Relation.EqvGen M.Adjacent 0 5 := trans h3 (.rel _ _ (Or.inr rfl))
    have h13 : Relation.EqvGen M.Adjacent 0 13 := trans h5 (.rel _ _ (Or.inr rfl))
    have h8 : Relation.EqvGen M.Adjacent 0 8 := trans h13 (.rel _ _ (Or.inr rfl))
    have h9 : Relation.EqvGen M.Adjacent 0 9 := trans h8 (.rel _ _ (Or.inl rfl))
    have h10 : Relation.EqvGen M.Adjacent 0 10 := trans h9 (.rel _ _ (Or.inr rfl))
    have h11 : Relation.EqvGen M.Adjacent 0 11 := trans h10 (.rel _ _ (Or.inl rfl))
    have h12 : Relation.EqvGen M.Adjacent 0 12 := trans h11 (.rel _ _ (Or.inr rfl))
    have h7 : Relation.EqvGen M.Adjacent 0 7 := trans h6 (.rel _ _ (Or.inl rfl))
    have h19 : Relation.EqvGen M.Adjacent 0 19 := trans h7 (.rel _ _ (Or.inr rfl))
    have h14 : Relation.EqvGen M.Adjacent 0 14 := trans h19 (.rel _ _ (Or.inr rfl))
    have h15 : Relation.EqvGen M.Adjacent 0 15 := trans h14 (.rel _ _ (Or.inl rfl))
    have h16 : Relation.EqvGen M.Adjacent 0 16 := trans h15 (.rel _ _ (Or.inr rfl))
    have h17 : Relation.EqvGen M.Adjacent 0 17 := trans h16 (.rel _ _ (Or.inl rfl))
    have h18 : Relation.EqvGen M.Adjacent 0 18 := trans h17 (.rel _ _ (Or.inr rfl))
    have hstep : ∀ d : Fin 20, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · exact h9
      · exact h10
      · exact h11
      · exact h12
      · exact h13
      · exact h14
      · exact h15
      · exact h16
      · exact h17
      · exact h18
      · exact h19
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 7 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 5 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 20 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 10 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 5 → List (Fin 20) :=
  ![[0, 6, 19, 17, 15, 7, 4, 13, 11, 9, 3], [8, 10, 12], [1], [14, 16, 18], [2, 5]]

noncomputable def indexedBoundary (i : Fin 5) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 20)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 5) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-- The letters read along the darts. -/
def vals : Fin 20 → G :=
  ![gc, gc⁻¹, gx, gx⁻¹, gx, gx⁻¹, gy, gy⁻¹, ga, ga⁻¹, ga, ga⁻¹, gb, gb⁻¹, gd, gd⁻¹, gd, gd⁻¹, ge,
    ge⁻¹]

def label (d : Fin 20) : RelLetter G Empty := .base (vals d)

/-- The relators `P` and `Q`. -/
def pinchW : Set (List (RelLetter G Empty)) := {pWord, qWord}

def piCell : RelatorCell M (face 2) pinchW where
  face := face 1
  face_ne_outer := (face_eq_iff 1 2).not.mpr (by decide)
  word := pWord
  word_mem := Set.mem_insert _ _
  conjugator := gx
  reversed := false

def rCell : RelatorCell M (face 2) pinchW where
  face := face 3
  face_ne_outer := (face_eq_iff 3 2).not.mpr (by decide)
  word := qWord
  word_mem := Set.mem_insert_of_mem _ rfl
  conjugator := gy
  reversed := false

/-- **The counterexample as a disc diagram**, with the relator cells `Π` and `R`. -/
noncomputable def pinchDiagram : DiscDiagram pinchW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [piCell, rCell]
  relatorCell_faces_nodup := by
    change [face 1, face 3].Nodup
    exact List.nodup_cons.mpr
      ⟨fun h => absurd ((face_eq_iff 1 3).mp (List.mem_singleton.mp h)) (by decide),
        List.nodup_singleton _⟩
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change pWord = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · rcases List.mem_singleton.mp hC with rfl
      change qWord = (boundary (face 3)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · right
      rw [boundary_face_darts]
      decide
    · exact Or.inl ⟨piCell, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · exact (hf rfl).elim
    · exact Or.inl ⟨rCell, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), rfl⟩
    · right
      rw [boundary_face_darts]
      decide
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance pinchDiagram_neZero : NeZero pinchDiagram.rCellCount := ⟨by decide⟩
instance pinchDiagram_ofNat (n : ℕ) : OfNat pinchDiagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 20) n)
instance pinchDiagram_decidableEq : DecidableEq pinchDiagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 20))

theorem pinchDiagram_rCellCount : pinchDiagram.rCellCount = 2 := rfl

theorem pinchDiagram_cell_zero_word : (Embedded.cell pinchDiagram 0).word = pWord := rfl

theorem pinchDiagram_cell_one_word : (Embedded.cell pinchDiagram 1).word = qWord := rfl

/-- The boundary word is the one letter `c`. -/
theorem pinchDiagram_boundaryWord : pinchDiagram.boundaryWord = [.base gc] := by
  change HullSC.RelWord.revInv ((boundary (face 2)).darts.map label) = _
  rw [boundary_face_darts]
  exact congrArg (fun g => [RelLetter.base g]) (inv_inv gc)

theorem pinchDiagram_cellDarts : Embedded.cellDarts pinchDiagram 0 = [8, 10, 12] := by
  change (boundary (face 1)).darts = _
  rw [boundary_face_darts]
  rfl

theorem pinchDiagram_outerDarts : Embedded.outerDarts pinchDiagram = [0] := by
  change ((boundary (face 2)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

/-- Membership in the base set, as a decidable list membership. -/
theorem mem_baseSet_iff (g : G) :
    g ∈ baseSet ↔ g ∈ ([ga, ga⁻¹, gb, gb⁻¹, gd, gd⁻¹, ge, ge⁻¹, gx, gx⁻¹, gy, gy⁻¹, gc, gc⁻¹] :
      List G) := by
  simp [baseSet]

/-- The labels of the diagram are letters of the symmetrized alphabet. -/
theorem pinchDiagram_letters :
    ∀ d, (symmetricLabelAlphabet D).IsLetter (pinchDiagram.label d) := by
  intro d
  refine Or.inl ((mem_baseSet_iff _).mpr ?_)
  fin_cases d <;> decide

/-! ## The pocket face set `{κ, R}` -/

/-- The face set `{κ, R}`. -/
def pinchFaces : Finset pinchDiagram.toCombMap.Face :=
  Finset.cons (face 0) {face 3} fun h =>
    absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

theorem face_mem_pinchFaces_iff (i : Fin 5) : face i ∈ pinchFaces ↔ i = 0 ∨ i = 3 :=
  Finset.mem_cons.trans (or_congr (face_eq_iff i 0) (Finset.mem_singleton.trans (face_eq_iff i 3)))

theorem pinchBoundaryDart_iff (d : Fin 20) :
    IsBoundaryDart pinchDiagram.toCombMap pinchFaces d ↔
      d ∈ ([4, 13, 11, 9, 3, 0] : List (Fin 20)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The six boundary darts of `{κ, R}`, in walk order from `e_2`. -/
def pinchCycle : BoundaryCycle pinchDiagram.toCombMap pinchFaces where
  cycle := ([4, 13, 11, 9, 3, 0] : List (Fin 20))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([4, 13, 11, 9, 3, 0] : List (Fin 20)).Nodup)
  cycle_mem_iff := fun d => (pinchBoundaryDart_iff d).symm

/-- The arc `[8,10,12]` of `Π`, all of it. -/
def pinchSourceArc : Embedded.CyclicArc (Embedded.cellDarts pinchDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 3
  length_le := by
    rw [pinchDiagram_cellDarts]
    decide

theorem pinchSourceArc_darts : pinchSourceArc.darts = [8, 10, 12] := by
  change ((Embedded.cellDarts pinchDiagram 0).drop 0 ++
    (Embedded.cellDarts pinchDiagram 0).take 0).take 3 = _
  rw [pinchDiagram_cellDarts]
  rfl

/-- The arc `[0]` of the exterior boundary, all of it. -/
def pinchTargetArc : Embedded.CyclicArc (Embedded.outerDarts pinchDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [pinchDiagram_outerDarts]
    decide

theorem pinchTargetArc_darts : pinchTargetArc.darts = [0] := by
  change ((Embedded.outerDarts pinchDiagram).drop 0 ++
    (Embedded.outerDarts pinchDiagram).take 0).take 1 = _
  rw [pinchDiagram_outerDarts]
  rfl

/-- The cycle of `{κ, R}` is the side `[4]`, the reversed arc `[13,11,9]` of `Π`, the side `[3]` and
the arc `[0]` of the exterior. -/
theorem pinch_decomposition :
    (pinchCycle : BoundaryCycle pinchDiagram.toCombMap pinchFaces).cycle =
      [4] ++ Embedded.invDarts pinchDiagram pinchSourceArc.darts ++ [3] ++
        pinchTargetArc.darts := by
  rw [pinchSourceArc_darts, pinchTargetArc_darts]
  decide

/-- A one-dart side labelled by a base letter has word norm at most one. -/
theorem pinch_side_norm {d : Fin 20} (hd : vals d ∈ baseSet) :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord pinchDiagram ([d] : List pinchDiagram.toCombMap.Dart))) ≤ 1 := by
  refine WordMetric.wordNorm_le_one_of_mem (Or.inl ?_)
  change vals d * 1 ∈ baseSet
  rwa [mul_one]

/-- **The pocket face set `{κ, R}`** at `ε = 1`, with source `Π` and kept cell `R`. -/
noncomputable def pinchK : PocketFaceSet D 1 pinchDiagram 0 1 where
  faces := pinchFaces
  outerFace_not_mem := fun h => absurd ((face_mem_pinchFaces_iff 2).mp h) (by decide)
  source := 0
  source_not_mem := fun h => absurd ((face_mem_pinchFaces_iff 1).mp h) (by decide)
  kept := ⟨1, by decide⟩
  kept_mem := (face_mem_pinchFaces_iff 3).mpr (Or.inr rfl)
  sourceArc := pinchSourceArc
  targetArc := pinchTargetArc
  firstSide := [4]
  secondSide := [3]
  boundary := pinchCycle
  decomposition := pinch_decomposition
  firstSide_length_le := Nat.le_refl 1
  secondSide_length_le := Nat.le_refl 1
  firstSide_norm_le := pinch_side_norm ((mem_baseSet_iff _).mpr (by decide))
  secondSide_norm_le := pinch_side_norm ((mem_baseSet_iff _).mpr (by decide))
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- The cycle `[4,13,11,9,3,0]` is a closed walk. -/
theorem pinchK_closedWalk : pinchK.ClosedWalk := by
  refine ⟨?_, vertexOf_eq_of_class (by decide)⟩
  exact (show ([4, 13, 11, 9, 3, 0] : List (Fin 20)).IsChain
      (fun d e => vertexClass (pinchAlpha d) = vertexClass e) by decide).imp
    fun _ _ h => vertexOf_eq_of_class h

#audit_axioms pinchDiagram
#audit_axioms pinchK
#audit_closed_axioms pinchDiagram_letters
#audit_closed_axioms pinchK_closedWalk
#audit_closed_axioms pinchDiagram_boundaryWord

end GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels
