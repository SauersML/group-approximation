import GroupApproximation.Manuscript.NonMF.Full.GL05c.Statement
import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The map of the counterexample to WO-GL05-2'

The combinatorial map underlying the refutation of `ExtremalEndBlockStatement`
(`Full/GL05c/Statement.lean`).  It has sixteen darts, three vertices, eight edges and seven faces.

* Edges: `{0,1}` is the loop `p` at `w`, `{2,3}` and `{4,5}` are `R1a : w → u` and `R1b : u → w`,
  `{6,7}` is the loop `q1` at `u`, `{8,9}` and `{12,13}` are `R2a : w → z` and `R2b : z → w`,
  `{10,11}` is the loop `q2` at `z`, and `{14,15}` is the loop `e` at `w`.
* Rotations: `w` is `0 ↦ 5 ↦ 2 ↦ 15 ↦ 11 ↦ 8 ↦ 14 ↦ 1 ↦ 0`, `u` is `3 ↦ 4 ↦ 7 ↦ 6 ↦ 3` and `z` is
  `9 ↦ 10 ↦ 13 ↦ 12 ↦ 9`.
* Faces: `P = [0]`, `R1 = [2,4]`, `Q1 = [6]`, `R2 = [8,10]`, `Q2 = [12]`, the source cell
  `S = [9,14,11,13]` and the exterior `O = [1,5,7,3,15]` (`faceDarts`).
* `planar`: the map is connected and has Euler characteristic `3 - 8 + 7 = 2`.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, Hull's small cancellation
theorem, through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c.Model

open Equiv GroupApproximation.GGT.VanKampen

/-- The edge involution: `{0,1}`, `{2,3}`, ..., `{14,15}`. -/
def mapAlpha : Perm (Fin 16) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  left_inv := by decide
  right_inv := by decide

/-- The rotation at the three vertices. -/
def mapSigma : Perm (Fin 16) where
  toFun := ![5, 0, 15, 4, 7, 2, 3, 6, 14, 10, 13, 8, 9, 12, 1, 11]
  invFun := ![1, 14, 5, 6, 3, 0, 7, 4, 11, 12, 9, 15, 13, 10, 8, 2]
  left_inv := by decide
  right_inv := by decide

/-- **The map of the counterexample** (sixteen darts). -/
def M : CombMap where
  Dart := Fin 16
  dartFintype := inferInstance
  alpha := mapAlpha
  sigma := mapSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance M_decidableEq : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 16))
instance M_ofNat (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 16) n)

/-- The face of each dart: `P`, `R1`, `Q1`, `R2`, `Q2`, `S`, `O` are `0, ..., 6`. -/
def faceClass : Fin 16 → Fin 7 := ![0, 6, 1, 6, 1, 6, 2, 6, 3, 5, 3, 5, 4, 5, 5, 6]

/-- A representative dart of each face. -/
def faceRep : Fin 7 → Fin 16 := ![0, 2, 6, 8, 12, 9, 1]

noncomputable def faceEquiv : M.Face ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma
    (![0, 0, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 0] : Fin 16 → Fin 3)
    (![0, 3, 9] : Fin 3 → Fin 16) (by decide) (by decide) (by decide)

/-- **The map is planar**, with three vertices, eight edges and seven faces. -/
theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 16, Relation.EqvGen M.Adjacent 0 d := by
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inr rfl)
      have h52 : Relation.EqvGen M.Adjacent 5 2 := .rel _ _ (Or.inr rfl)
      have h215 : Relation.EqvGen M.Adjacent 2 15 := .rel _ _ (Or.inr rfl)
      have h1511 : Relation.EqvGen M.Adjacent 15 11 := .rel _ _ (Or.inr rfl)
      have h118 : Relation.EqvGen M.Adjacent 11 8 := .rel _ _ (Or.inr rfl)
      have h814 : Relation.EqvGen M.Adjacent 8 14 := .rel _ _ (Or.inr rfl)
      have h141 : Relation.EqvGen M.Adjacent 14 1 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h34 : Relation.EqvGen M.Adjacent 3 4 := .rel _ _ (Or.inr rfl)
      have h47 : Relation.EqvGen M.Adjacent 4 7 := .rel _ _ (Or.inr rfl)
      have h76 : Relation.EqvGen M.Adjacent 7 6 := .rel _ _ (Or.inr rfl)
      have h89 : Relation.EqvGen M.Adjacent 8 9 := .rel _ _ (Or.inl rfl)
      have h910 : Relation.EqvGen M.Adjacent 9 10 := .rel _ _ (Or.inr rfl)
      have h1013 : Relation.EqvGen M.Adjacent 10 13 := .rel _ _ (Or.inr rfl)
      have h1312 : Relation.EqvGen M.Adjacent 13 12 := .rel _ _ (Or.inr rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 := .trans _ _ _ h05 h52
      have h015 : Relation.EqvGen M.Adjacent 0 15 := .trans _ _ _ h02 h215
      have h011 : Relation.EqvGen M.Adjacent 0 11 := .trans _ _ _ h015 h1511
      have h08 : Relation.EqvGen M.Adjacent 0 8 := .trans _ _ _ h011 h118
      have h014 : Relation.EqvGen M.Adjacent 0 14 := .trans _ _ _ h08 h814
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .trans _ _ _ h014 h141
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .trans _ _ _ h02 h23
      have h04 : Relation.EqvGen M.Adjacent 0 4 := .trans _ _ _ h03 h34
      have h07 : Relation.EqvGen M.Adjacent 0 7 := .trans _ _ _ h04 h47
      have h06 : Relation.EqvGen M.Adjacent 0 6 := .trans _ _ _ h07 h76
      have h09 : Relation.EqvGen M.Adjacent 0 9 := .trans _ _ _ h08 h89
      have h010 : Relation.EqvGen M.Adjacent 0 10 := .trans _ _ _ h09 h910
      have h013 : Relation.EqvGen M.Adjacent 0 13 := .trans _ _ _ h010 h1013
      have h012 : Relation.EqvGen M.Adjacent 0 12 := .trans _ _ _ h013 h1312
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
      · exact h07
      · exact h08
      · exact h09
      · exact h010
      · exact h011
      · exact h012
      · exact h013
      · exact h014
      · exact h015
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 7 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 16 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 8 := by omega
    rw [heq]
    norm_num

/-! ## Faces and their boundaries -/

/-- The face with index `i`. -/
def face (i : Fin 7) : M.Face := M.faceOf (faceRep i)

theorem faceEquiv_face (i : Fin 7) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 16) (i : Fin 7) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 7) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

/-- The boundary darts of each face, in face-permutation order. -/
def faceDarts : Fin 7 → List (Fin 16) :=
  ![[0], [2, 4], [6], [8, 10], [12], [9, 14, 11, 13], [1, 5, 7, 3, 15]]

noncomputable def indexedBoundary (i : Fin 7) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 16)); fin_cases i <;> decide
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

/-- The chosen boundary of each face. -/
noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

theorem boundary_face_darts (i : Fin 7) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

end GroupApproximation.Full.GL05c.Model

#audit_axioms GroupApproximation.Full.GL05c.Model.M
#audit_axioms GroupApproximation.Full.GL05c.Model.planar
#audit_axioms GroupApproximation.Full.GL05c.Model.faceOf_eq_face
#audit_axioms GroupApproximation.Full.GL05c.Model.boundary_face_darts
