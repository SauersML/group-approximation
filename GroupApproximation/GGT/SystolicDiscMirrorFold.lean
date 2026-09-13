import GroupApproximation.GGT.SystolicDiscMirrorFoldPinchedStage
import GroupApproximation.GGT.SystolicDiscMirrorFoldDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# HC6: the mirror fold

Let `d` be a dart of a triangulated disc with both sides on inner faces, whose two triangles
have third vertices carrying one label.  The disc folds to a triangulated disc with the same
boundary and two triangles fewer.

* `mirrorFoldPinched`: the two third vertices are one vertex of the disc.  Deleting the edge
  of `d` leaves a face through that vertex twice; splitting the vertex cuts the map in two, and
  the side of the exterior face loses a digon (`FoldStage.exists_disc_of_pinch`).
* `mirrorFold`: HC6 for every triangle complex, from `mirrorFoldPinched` and
  `mirrorFoldDistinct`.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u}

/-- **HC6, a common third vertex.** -/
theorem mirrorFoldPinched (X : TriangleComplex V) : MirrorFoldPinchedStatement X := by
  intro γ T d hd had hthird
  have hcyc := (FoldStage.exists_outer_rest T).choose_spec
  have hout : ∀ z, z ∈ (FoldStage.toStage T).cyc → T.map.faceOf z = T.outer := fun z hz => by
    have h := (hcyc.mem_iff z).mp hz
    rwa [List.head_cons, T.base_outer] at h
  have h2 : T.map.vertexOf (T.map.facePerm (T.map.facePerm d)) =
      T.map.vertexOf (T.map.facePerm (T.map.facePerm (T.map.alpha d))) := by
    have h := hthird
    unfold TriangulatedDisc.third at h
    rwa [perm_pow_two_apply, perm_pow_two_apply] at h
  have P : FoldStage.IsPinch (FoldStage.toStage T) d :=
    { planar := T.planar
      good := fun _ h => h
      not_mem := fun hm => hd (hout d hm)
      not_mem_alpha := fun hm => had (hout _ hm)
      face_ne := (T.faceOf_alpha_ne_of_inner hd).symm
      pinch := (CombMap.vertexOf_eq_iff T.map _ _).mp h2 }
  obtain ⟨D, hD⟩ := FoldStage.exists_disc_of_pinch P (FoldStage.toStage_boundary T)
  refine ⟨D, ?_⟩
  have h1 : 1 ≤ T.map.faceCount := T.one_le_faceCount
  have h3 : D.innerFaceCount + 3 ≤ T.map.faceCount := hD
  show D.innerFaceCount + 2 ≤ T.map.faceCount - 1
  omega

/-- **HC6, the mirror fold**, for every triangle complex. -/
theorem mirrorFold (X : TriangleComplex V) : MirrorFoldStatement X :=
  mirrorFoldStatement_of_cases (mirrorFoldDistinct X) (mirrorFoldPinched X)

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.mirrorFoldPinched
#audit_axioms GroupApproximation.Systolic.mirrorFold
