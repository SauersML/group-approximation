import GroupApproximation.GGT.VanKampen.FaceSetEar
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# A face set with a spur has no peelable ear

`Embedded.FaceSetEarStatement` asks every face set with a `FaceSetBoundary` for a
`FaceSetEar`: a selected face whose boundary, read from a suitable dart, begins
with a contiguous arc of the boundary cycle, such that erasing the face leaves
either nothing or a boundary cycle of the remaining faces.

The map below has four darts and two edges.  Its face cycles are `[0,1,2]` and
`[3]`.  The edge `{0,1}` is a spur inside the first face, and the second face is
the outer face.  The group is trivial, so the first face is a G-cell and the
diagram has no relator cells.  The face set `{face 0}` has the boundary cycle
`[2]`.  Erasing its only face must leave nothing, so the arc is the whole cycle
`[2]` and the rest of the face boundary is empty; but that boundary also carries
the spur darts `0` and `1`.  So `FaceSetEarStatement` and
`FaceSetEarDataStatement` are false.  The boundary walk of a face set need not
read a face boundary once, and a shelling producer must erase spurs
(`FaceSetWordHomotopy.eraseAlphaPair`) as well as faces.
-/

namespace GroupApproximation.GGT.VanKampen.FaceSetEarSpurCounterexample

open Equiv

def alpha : Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 4
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 4))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 4) n)

def faceClass : Fin 4 → Fin 2 := ![0, 0, 0, 1]
def faceRep : Fin 2 → Fin 4 := ![0, 3]

noncomputable def faceEquiv : M.Face ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 2) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 2) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 4) (i : Fin 2) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 2) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 0, 0] : Fin 4 → Fin 2)
    (![0, 1] : Fin 2 → Fin 4) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 4, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 :=
        .rel _ _ (Or.inl rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 :=
        .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 :=
        .rel _ _ (Or.inl rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact .trans _ _ _ h02 h23
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 2 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 4 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 2 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 2 → List (Fin 4) := ![[0, 1, 2], [3]]

noncomputable def indexedBoundary (i : Fin 2) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 4)); fin_cases i <;> decide
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

def label (_ : Fin 4) : RelLetter Unit Empty := .base ()

def W : Set (List (RelLetter Unit Empty)) := ∅

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := fun _ => rfl
  outerFace := face 1
  faceBoundary := boundary
  relatorCells := []
  relatorCell_faces_nodup := by simp
  relatorCell_word := by
    intro C hC
    cases hC
  inner_face := fun _ _ => Or.inr (Subsingleton.elim _ _)
  boundary_product := Subsingleton.elim _ _

instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 4) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 4))

def faces : Finset diagram.toCombMap.Face := {face 0}

theorem isBoundaryDart_iff (d : Fin 4) :
    Embedded.IsBoundaryDart diagram faces d ↔ d = 2 := by
  change (M.faceOf d ∈ ({face 0} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 0} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The boundary cycle `[2]` closes up through the spur: after `2` the face
reaches `0`, and crossing the internal edge `{0,1}` returns to `2`. -/
theorem step22 : Embedded.BoundaryStep diagram faces 2 2 := by
  refine ⟨(isBoundaryDart_iff 2).mpr rfl, (isBoundaryDart_iff 2).mpr rfl, ?_⟩
  have hmove : Embedded.InternalBoundaryMove diagram faces 0 2 :=
    ⟨Finset.mem_singleton.mpr ((faceOf_eq_face 0 0).mpr (by decide)),
      Finset.mem_singleton.mpr ((faceOf_eq_face 1 0).mpr (by decide)), by decide⟩
  have hfp : diagram.toCombMap.facePerm 2 = 0 := by decide
  rw [hfp]
  exact Relation.ReflTransGen.single hmove

noncomputable def regionBoundary : Embedded.FaceSetBoundary diagram faces where
  faces_nonempty := Finset.singleton_nonempty _
  all_gCells := by
    intro f hf
    have h : f = face 0 := Finset.mem_singleton.mp hf
    subst f
    exact ⟨(face_eq_iff 0 1).not.mpr (by decide), Subsingleton.elim _ _⟩
  cycle := [2]
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := by decide
  cycle_mem_iff := fun d => List.mem_singleton.trans (isBoundaryDart_iff d).symm
  cycle_chain := List.isChain_singleton _
  cycle_closes := step22

noncomputable local instance faceDecidableEqSpur :
    DecidableEq diagram.toCombMap.Face := Classical.decEq _

/-- The face set `{face 0}` has a boundary cycle but no peelable ear. -/
theorem no_ear : ¬ Nonempty (Embedded.FaceSetEar regionBoundary) := by
  rintro ⟨E⟩
  have hface : E.face = face 0 := Finset.mem_singleton.mp E.face_mem
  rcases E.remainder with ⟨_, hword⟩ | ⟨boundary', _⟩
  · obtain ⟨hleft, hafter⟩ := List.append_eq_nil_iff.mp hword
    obtain ⟨hbefore, hinterior⟩ := List.append_eq_nil_iff.mp hleft
    have hinterior' : E.interior = [] := by
      simpa [Embedded.invDarts] using hinterior
    have harc : E.arc = [2] := by
      have h := E.cycle_eq
      rw [hbefore, hafter, List.nil_append, List.append_nil] at h
      exact h.symm
    have h0 : (0 : diagram.toCombMap.Dart) ∈ (diagram.faceBoundary E.face).darts := by
      refine ((diagram.faceBoundary E.face).mem_iff 0).mpr ?_
      rw [hface]
      exact (faceOf_eq_face 0 0).mpr (by decide)
    have h1 : (0 : diagram.toCombMap.Dart) ∈
        (diagram.faceBoundary E.face).darts.rotate E.faceRotation :=
      List.mem_rotate.mpr h0
    rw [E.face_eq, harc, hinterior'] at h1
    exact absurd h1 (by decide)
  · obtain ⟨x, hx⟩ := boundary'.faces_nonempty
    have hmem := Finset.mem_erase.mp hx
    exact hmem.1 ((Finset.mem_singleton.mp hmem.2).trans hface.symm)

/-- The ear statement is false: a spur inside a selected G-face gives a face
set with a boundary cycle and no peelable ear. -/
theorem not_faceSetEarStatement : ¬ Embedded.FaceSetEarStatement.{0, 0, 0} :=
  fun h => no_ear (h regionBoundary)

/-- The ear-data statement is false, since it would give the ear statement. -/
theorem not_faceSetEarDataStatement : ¬ Embedded.FaceSetEarDataStatement.{0, 0, 0} :=
  fun h => not_faceSetEarStatement (Embedded.faceSetEarStatement_of_earData h)

#audit_closed_axioms not_faceSetEarStatement
#audit_closed_axioms not_faceSetEarDataStatement

end GroupApproximation.GGT.VanKampen.FaceSetEarSpurCounterexample
