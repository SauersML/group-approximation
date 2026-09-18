import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWholeSectionWrapModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The map of the counterexample to `roseLobeBlk_BlockStatement`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

A planar map with sixteen darts, the edges `{2i, 2i+1}`, three vertices and seven faces.  The
rotation has the cycles `(0 14 4 9 13 7 10 2 3 6 12 8 5)`, `(1 15)` and `(11)`.  The faces
(orbits of `facePerm = sigma ∘ alpha`) are `[0,15,4]`, `[1,14]`, `[2,6,10,11]`, `[3]`, `[5,9]`,
`[7,12]` and `[8,13]`.  So `V - E + F = 3 - 8 + 7 = 2`.

This is the first failing configuration of the gl-p10-72 search (`fails_s5.pkl`, entry `0`).
The disc diagram is in `P10BlkBlock.Diagram`, and the refutation in `P10BlkBlock.Refute`.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

open Equiv

def pAlpha : Perm (Fin 16) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]
  left_inv := by decide
  right_inv := by decide

def pSigma : Perm (Fin 16) where
  toFun := ![14, 15, 3, 6, 9, 0, 12, 10, 5, 13, 2, 11, 8, 7, 4, 1]
  invFun := ![5, 15, 10, 2, 14, 8, 3, 13, 12, 4, 7, 11, 6, 9, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The map with sixteen darts, three vertices and seven faces. -/
def M : CombMap where
  Dart := Fin 16
  dartFintype := inferInstance
  alpha := pAlpha
  sigma := pSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance instDecEqM : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 16))
instance instOfNatM (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 16) n)

def faceClass : Fin 16 → Fin 7 := ![0, 1, 2, 3, 0, 4, 2, 5, 6, 4, 2, 2, 5, 6, 1, 0]
def faceRep : Fin 7 → Fin 16 := ![0, 1, 2, 3, 5, 7, 8]

noncomputable def faceEquiv : M.Face ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

def face (i : Fin 7) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 7) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 16) (i : Fin 7) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 7) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

theorem faceOf_eq_face' (x : Fin 16) : M.faceOf x = face (faceClass x) :=
  (faceOf_eq_face x _).mpr rfl

def vClass : Fin 16 → Fin 3 := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1]
def vRep : Fin 3 → Fin 16 := ![0, 1, 11]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma vClass vRep (by decide) (by decide) (by decide)

theorem vClass_iff (d e : Fin 16) : M.vertexOf d = M.vertexOf e ↔ vClass d = vClass e := by
  rw [← vertexEquiv.injective.eq_iff]
  rfl

theorem planar : M.IsPlanar := by
  constructor
  · have s {a b : M.Dart} (h : M.sigma a = b) : Relation.EqvGen M.Adjacent a b :=
      .rel _ _ (Or.inr h)
    have t {a b : M.Dart} (h : M.alpha a = b) : Relation.EqvGen M.Adjacent a b :=
      .rel _ _ (Or.inl h)
    have tr {a b c : M.Dart} (h1 : Relation.EqvGen M.Adjacent a b)
        (h2 : Relation.EqvGen M.Adjacent b c) : Relation.EqvGen M.Adjacent a c :=
      .trans _ _ _ h1 h2
    have h14 : Relation.EqvGen M.Adjacent 0 14 := s rfl
    have h4 := tr h14 (s (b := 4) rfl)
    have h9 := tr h4 (s (b := 9) rfl)
    have h13 := tr h9 (s (b := 13) rfl)
    have h7 := tr h13 (s (b := 7) rfl)
    have h10 := tr h7 (s (b := 10) rfl)
    have h2 := tr h10 (s (b := 2) rfl)
    have h3 := tr h2 (s (b := 3) rfl)
    have h6 := tr h3 (s (b := 6) rfl)
    have h12 := tr h6 (s (b := 12) rfl)
    have h8 := tr h12 (s (b := 8) rfl)
    have h5 := tr h8 (s (b := 5) rfl)
    have h1 : Relation.EqvGen M.Adjacent 0 1 := t rfl
    have h15 := tr h1 (s (b := 15) rfl)
    have h11 := tr h10 (t (b := 11) rfl)
    have hstep : ∀ d : Fin 16, Relation.EqvGen M.Adjacent 0 d := by
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

def faceDarts : Fin 7 → List (Fin 16) :=
  ![[0, 15, 4], [1, 14], [2, 6, 10, 11], [3], [5, 9], [7, 12], [8, 13]]

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

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 7) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.pAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.pSigma
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.M
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.instDecEqM
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.instOfNatM
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceRep
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.face
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceEquiv_face
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceOf_eq_face
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.face_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceOf_eq_face'
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.vClass
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.vRep
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.vertexEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.vClass_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.planar
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceDarts
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.indexedBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.boundary
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.boundary_face_darts
