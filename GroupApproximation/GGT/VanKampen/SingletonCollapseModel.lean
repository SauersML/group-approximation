import GroupApproximation.GGT.VanKampen.SingletonReclosed
import GroupApproximation.GGT.VanKampen.SelfContiguityModel

/-!
# An actual exact singleton disc-region construction

The triangle in the self-contiguity model has no internally paired dart.
Its singleton collapse therefore has its complete original boundary and is
planar, with both topological fields constructed by the general proof.
-/

namespace GroupApproximation.GGT.VanKampen.SingletonCollapseModel

open Surgery.MapCollapse SelfContiguityModel

theorem triangle_noInternal : NoInternalFaceDart M (face 0) := by
  have hfinite : ∀ d : Fin 6, faceClass d = 0 → faceClass (alpha d) ≠ 0 := by decide
  intro d hd ha
  exact hfinite d ((faceOf_eq_face d 0).mp hd) ((faceOf_eq_face (M.alpha d) 0).mp ha)

/-- The original face boundary is retained by an actual planar collapse. -/
theorem exists_planar_exact_singleton :
    ∃ region : IsDiscRegion M {face 0},
      region.toBoundaryCycle.cycle = [0, 1, 2] ∧
        (replaceGRegion M {face 0} region).IsPlanar := by
  let region := SingletonReclosed.discRegion M (face 0) (boundary (face 0))
    triangle_noInternal planar.1
  refine ⟨region, ?_, replaceGRegion_planar M {face 0} region planar⟩
  change (boundary (face 0)).darts = [0, 1, 2]
  rw [boundary_face_darts]
  rfl

end GroupApproximation.GGT.VanKampen.SingletonCollapseModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.SingletonCollapseModel.exists_planar_exact_singleton
