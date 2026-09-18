import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWholeSectionWrapModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The map of the counterexample to `RoseExtremalJunctionStatement`

Lane gl-p10-51.  The 24-dart subdivided G-face model of lane gl-p10-48.

A planar map with 24 darts.  The edges are `{2i, 2i+1}`.  It has seven vertices and seven faces.
The rotation has the cycles `(0 19 2 14 23 8 15 1)`, `(3 16)`, `(4 17 6 5)`, `(7 18)`,
`(9 20)`, `(10 21 12 11)` and `(13 22)`.  The faces are `[0]`, `[19,7,5,17,3,14,1]`,
`[2,16,6,18]`, `[4]`, `[8,20,12,22]`, `[15,23,13,11,21,9]` and `[10]`.  So
`V - E + F = 7 - 12 + 7 = 2`.

Proof route: every fact is a kernel `decide` over `Fin 24`, or an orbit classifier
(`OrbitClassifier.orbitEquiv`).

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open Equiv

def roseJunctionRefute_pAlpha : Perm (Fin 24) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]
  left_inv := by decide
  right_inv := by decide

def roseJunctionRefute_pSigma : Perm (Fin 24) where
  toFun := ![19, 0, 14, 16, 17, 4, 5, 18, 15, 20, 21, 10, 11, 22, 23, 1, 3, 6, 7, 2, 9, 12, 13, 8]
  invFun := ![1, 15, 19, 16, 5, 6, 17, 18, 23, 20, 11, 12, 21, 22, 2, 8, 3, 4, 7, 0, 9, 10, 13, 14]
  left_inv := by decide
  right_inv := by decide

/-- The map with 24 darts, seven vertices and seven faces. -/
def roseJunctionRefute_M : CombMap where
  Dart := Fin 24
  dartFintype := inferInstance
  alpha := roseJunctionRefute_pAlpha
  sigma := roseJunctionRefute_pSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance roseJunctionRefute_instDecEqM : DecidableEq roseJunctionRefute_M.Dart :=
  inferInstanceAs (DecidableEq (Fin 24))
instance roseJunctionRefute_instOfNatM (n : ℕ) : OfNat roseJunctionRefute_M.Dart n :=
  inferInstanceAs (OfNat (Fin 24) n)

def roseJunctionRefute_faceClass : Fin 24 → Fin 7 :=
  ![0, 1, 2, 1, 3, 1, 2, 1, 4, 5, 6, 5, 4, 5, 1, 5, 2, 1, 2, 1, 4, 5, 4, 5]
def roseJunctionRefute_faceRep : Fin 7 → Fin 24 := ![0, 19, 2, 4, 8, 15, 10]

noncomputable def roseJunctionRefute_faceEquiv : roseJunctionRefute_M.Face ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv roseJunctionRefute_M.facePerm roseJunctionRefute_faceClass
    roseJunctionRefute_faceRep (by decide) (by decide) (by decide)

def roseJunctionRefute_face (i : Fin 7) : roseJunctionRefute_M.Face :=
  roseJunctionRefute_M.faceOf (roseJunctionRefute_faceRep i)

@[simp] theorem roseJunctionRefute_faceEquiv_face (i : Fin 7) :
    roseJunctionRefute_faceEquiv (roseJunctionRefute_face i) = i := by
  change roseJunctionRefute_faceClass (roseJunctionRefute_faceRep i) = i
  fin_cases i <;> rfl

theorem roseJunctionRefute_faceOf_eq_face (d : Fin 24) (i : Fin 7) :
    roseJunctionRefute_M.faceOf d = roseJunctionRefute_face i ↔
      roseJunctionRefute_faceClass d = i := by
  rw [← roseJunctionRefute_faceEquiv.injective.eq_iff, roseJunctionRefute_faceEquiv_face]
  rfl

theorem roseJunctionRefute_face_eq_iff (i j : Fin 7) :
    roseJunctionRefute_face i = roseJunctionRefute_face j ↔ i = j := by
  rw [← roseJunctionRefute_faceEquiv.injective.eq_iff, roseJunctionRefute_faceEquiv_face,
    roseJunctionRefute_faceEquiv_face]

theorem roseJunctionRefute_faceOf_eq_face' (x : Fin 24) :
    roseJunctionRefute_M.faceOf x = roseJunctionRefute_face (roseJunctionRefute_faceClass x) :=
  (roseJunctionRefute_faceOf_eq_face x _).mpr rfl

def roseJunctionRefute_vClass : Fin 24 → Fin 7 :=
  ![0, 0, 0, 1, 2, 2, 2, 3, 0, 4, 5, 5, 5, 6, 0, 0, 1, 2, 3, 0, 4, 5, 6, 0]
def roseJunctionRefute_vRep : Fin 7 → Fin 24 := ![0, 3, 4, 7, 9, 10, 13]

noncomputable def roseJunctionRefute_vertexEquiv : roseJunctionRefute_M.Vertex ≃ Fin 7 :=
  OrbitClassifier.orbitEquiv roseJunctionRefute_M.sigma roseJunctionRefute_vClass
    roseJunctionRefute_vRep (by decide) (by decide) (by decide)

theorem roseJunctionRefute_vClass_iff (d e : Fin 24) :
    roseJunctionRefute_M.vertexOf d = roseJunctionRefute_M.vertexOf e ↔
      roseJunctionRefute_vClass d = roseJunctionRefute_vClass e := by
  rw [← roseJunctionRefute_vertexEquiv.injective.eq_iff]
  rfl

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_pAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_pSigma
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_M
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_instDecEqM
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_instOfNatM
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceRep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceEquiv_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceOf_eq_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_face_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_faceOf_eq_face'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_vClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_vRep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_vertexEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_vClass_iff
