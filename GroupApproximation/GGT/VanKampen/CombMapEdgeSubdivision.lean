import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.GGT.VanKampen.CombMapEdgePlanarity

/-!
# Subdividing an edge by splitting its initial vertex

Insert an edge across the corresponding dual face, then dualize back. The
chosen corners are the successor of the old dart and the old dart, in that
order. This makes the fresh negative dart precede the old dart on the
subdivided path, even when the old initial vertex has degree one.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeSubdivision

open Equiv PermOrbitInsert
universe u

noncomputable abbrev toCombMap (M : CombMap.{u}) (a : M.Dart) : CombMap.{u} :=
  (EdgeInsertion.toCombMap M.dual (M.sigma a) a).dual

theorem dual_corners_face_eq (M : CombMap.{u}) (a : M.Dart) :
    M.dual.faceOf (M.sigma a) = M.dual.faceOf a := by
  rw [M.dual.faceOf_eq_iff]
  change (@Perm.SameCycle M.Dart M.dual.facePerm (M.sigma a) a)
  rw [M.dual_facePerm]
  exact Perm.SameCycle.rfl.apply_left

theorem facePerm_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a).facePerm = insertBefore (insertBefore M.facePerm (M.sigma a)) (some a) :=
  (EdgeInsertion.toCombMap M.dual (M.sigma a) a).dual_facePerm

theorem vertexCount_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a).vertexCount = M.vertexCount + 1 := by
  rw [CombMap.dual_vertexCount, EdgeInsertion.faceCount_eq M.dual _ _ (dual_corners_face_eq M a),
    M.dual_faceCount]

theorem edgeCount_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a).edgeCount = M.edgeCount + 1 := by
  rw [CombMap.dual_edgeCount, EdgeInsertion.edgeCount_eq, M.dual_edgeCount]

theorem faceCount_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a).faceCount = M.faceCount := by
  rw [CombMap.dual_faceCount, EdgeInsertion.vertexCount_eq, M.dual_vertexCount]

theorem planar (M : CombMap.{u}) (a : M.Dart) (h : M.IsPlanar) : (toCombMap M a).IsPlanar :=
  CombMap.dual_planar _ (EdgeInsertion.planar M.dual _ _ (M.dual_planar h) (dual_corners_face_eq M a))

/-- Face orbits are retained by the two insertions into their rotations. -/
def orbitEquivOfEq {D : Type u} {p q : Perm D} (h : p = q) :
    CombMap.Orbit p ≃ CombMap.Orbit q := Equiv.cast (congrArg CombMap.Orbit h)

@[simp] theorem orbitEquivOfEq_mk {D : Type u} {p q : Perm D} (h : p = q) (d : D) :
    orbitEquivOfEq h (Quotient.mk'' d) = Quotient.mk'' d := by
  subst q
  rfl

noncomputable def faceEquiv (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a).Face ≃ M.Face :=
  (orbitEquivOfEq (facePerm_eq M a)).trans
    ((PermOrbitInsert.orbitEquiv (insertBefore M.facePerm (M.sigma a)) (some a)).trans
      (PermOrbitInsert.orbitEquiv M.facePerm (M.sigma a)))

theorem faceEquiv_embed (M : CombMap.{u}) (a d : M.Dart) :
    faceEquiv M a ((toCombMap M a).faceOf (EdgeInsertion.embed M d)) = M.faceOf d := by
  simp only [faceEquiv, Equiv.trans_apply, CombMap.faceOf, orbitEquivOfEq_mk]
  rfl

theorem faceEquiv_none (M : CombMap.{u}) (a : M.Dart) :
    faceEquiv M a ((toCombMap M a).faceOf none) = M.faceOf a := by
  simp only [faceEquiv, Equiv.trans_apply, CombMap.faceOf, orbitEquivOfEq_mk]
  rfl

theorem faceEquiv_positive (M : CombMap.{u}) (a : M.Dart) :
    faceEquiv M a ((toCombMap M a).faceOf (some none)) = M.faceOf (M.alpha a) := by
  simp only [faceEquiv, Equiv.trans_apply, CombMap.faceOf, orbitEquivOfEq_mk]
  change M.faceOf (M.sigma a) = M.faceOf (M.alpha a)
  have h := M.faceOf_facePerm (M.alpha a)
  change M.faceOf (M.sigma (M.alpha (M.alpha a))) = _ at h
  simpa only [M.alpha_involutive a] using h

end GroupApproximation.GGT.VanKampen.EdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.facePerm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.vertexCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.edgeCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.planar
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.faceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.faceEquiv_positive
