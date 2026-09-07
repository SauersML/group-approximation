import GroupApproximation.GGT.VanKampen.SurgeryFacePartition
import GroupApproximation.Meta.AxiomGuard

/-!
# Faces of the reclosed map before a disc certificate

The actual face classification and count use only the specified boundary
cycle. They do not require connectedness or Euler preservation as inputs.
These proofs are available when constructing the historical IsDiscRegion
certificate, before either of its topological fields has been established.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe v

theorem reclosedMap_facePerm_eq (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    (reclosedMap M faces boundary).facePerm =
      (keptSplitEquiv M faces).symm.permCongr
        (Equiv.sumCongr (outsideFacePerm M faces) boundary.boundaryPerm) :=
  (reclosedMap_facePerm M faces boundary).trans
    (reclosedFacePerm_eq_permCongr M faces boundary)

/-- The faces of the replaced map are the old faces outside the region together
with the one new face. -/
noncomputable def reclosedFaceEquiv (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces) :
    (reclosedMap M faces boundary).Face ≃
      {f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1} :=
  (orbitCongrOfEq (reclosedMap_facePerm_eq M faces boundary)).trans
    (((orbitPermCongr (keptSplitEquiv M faces).symm
          (Equiv.sumCongr (outsideFacePerm M faces)
            boundary.boundaryPerm)).symm).trans
      ((orbitSumCongr (outsideFacePerm M faces)
          boundary.boundaryPerm).trans
        (Equiv.sumCongr (outsideOrbitEquiv M faces)
          (boundaryOrbitEquivPUnit M faces boundary))))

/-- The face of a retained dart, before the split is evaluated. -/
theorem reclosedFaceEquiv_faceOf (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces)
    (d : KeptDart M faces) :
    reclosedFaceEquiv M faces boundary
        ((reclosedMap M faces boundary).faceOf d) =
      Equiv.sumCongr (outsideOrbitEquiv M faces)
        (boundaryOrbitEquivPUnit M faces boundary)
        (orbitSumCongr (outsideFacePerm M faces)
          boundary.boundaryPerm
          (Quotient.mk'' (keptSplitEquiv M faces d))) :=
  rfl

/-- A retained dart based outside the region keeps its old face. -/
theorem reclosedFaceEquiv_faceOf_notMem (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∉ faces) :
    reclosedFaceEquiv M faces boundary
        ((reclosedMap M faces boundary).faceOf d) =
      Sum.inl ⟨M.faceOf d.1, hd⟩ := by
  have hbase := reclosedFaceEquiv_faceOf M faces boundary d
  rw [keptSplitEquiv_apply_of_notMem M faces d hd] at hbase
  exact hbase

/-- A retained dart based inside the region lands on the new face. -/
theorem reclosedFaceEquiv_faceOf_mem (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∈ faces) :
    reclosedFaceEquiv M faces boundary
        ((reclosedMap M faces boundary).faceOf d) =
      Sum.inr PUnit.unit := by
  have hbase := reclosedFaceEquiv_faceOf M faces boundary d
  rw [keptSplitEquiv_apply_of_mem M faces d hd] at hbase
  exact hbase

/-! ## The face count of the replacement -/

/-- Replacing a region by one face leaves the number of faces outside the
region and adds one. -/
theorem reclosedMap_faceCount (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    (reclosedMap M faces boundary).faceCount + faces.card =
      M.faceCount + 1 := by
  classical
  have hmem : Nat.card {f : M.Face // f ∈ faces} = faces.card :=
    Nat.card_eq_finsetCard faces
  have hcompl : Nat.card {f : M.Face // f ∈ faces} +
      Nat.card {f : M.Face // f ∉ faces} = M.faceCount := by
    have hcongr : Nat.card
        ({f : M.Face // f ∈ faces} ⊕ {f : M.Face // f ∉ faces}) =
        Nat.card M.Face :=
      Nat.card_congr (Equiv.sumCompl (fun f : M.Face => f ∈ faces))
    rw [Nat.card_sum] at hcongr
    exact hcongr
  have hunit : Nat.card PUnit.{v + 1} = 1 := Nat.card_unique
  have hnew : (reclosedMap M faces boundary).faceCount =
      Nat.card {f : M.Face // f ∉ faces} + 1 := by
    have hcongr : Nat.card ((reclosedMap M faces boundary).Face) =
        Nat.card ({f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1}) :=
      Nat.card_congr (reclosedFaceEquiv M faces boundary)
    rw [Nat.card_sum, hunit] at hcongr
    exact hcongr
  rw [hnew, ← hmem, ← hcompl]
  omega

/-- Replacing a region of at least two faces strictly drops the face count. -/
theorem reclosedMap_faceCount_lt (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hcard : 2 ≤ faces.card) :
    (reclosedMap M faces boundary).faceCount < M.faceCount := by
  have hcount := reclosedMap_faceCount M faces boundary
  omega

/-- Replacing a single face leaves the face count unchanged. -/
theorem reclosedMap_faceCount_of_card_eq_one (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces)
    (hcard : faces.card = 1) :
    (reclosedMap M faces boundary).faceCount = M.faceCount := by
  have hcount := reclosedMap_faceCount M faces boundary
  omega

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedFaceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_faceCount
