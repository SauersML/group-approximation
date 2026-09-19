import GroupApproximation.GGT.VanKampen.PermOrbitRestrict
import GroupApproximation.GGT.VanKampen.PermOrbitSum
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# The faces of a reclosed map

`Surgery.MapCollapse.replaceGRegion` deletes every edge internal to a selected
face set and recloses the region along its oriented boundary cycle.  This file
describes the faces of the result: they are the faces of the old map based
outside the region, together with one new face.

The face permutation after reclosing is an equivalence conjugating a sum of two
permutations, so the orbit lemmas of `PermOrbitTransport`, `PermOrbitSum` and
`PermOrbitRestrict` apply.  The outside summand is the old face rotation
restricted to the darts based outside the region, and its orbits are exactly the
old faces outside the region.  The boundary summand is the cyclic successor on
the boundary enumeration, which is a single cycle, so it has one orbit.

Two computation rules pin the equivalence down on darts: a retained dart based
outside the region keeps its old face, and a retained dart based inside it lands
on the new face.  The face count of the replacement then drops by one less than
the number of selected faces.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe v

/-! ## The outside face permutation is a restriction -/

/-- Face rotation preserves being based outside the selected face set. -/
theorem faceOf_notMem_facePerm_iff (M : CombMap.{v}) (faces : Finset M.Face)
    (d : M.Dart) :
    M.faceOf (M.facePerm d) ∉ faces ↔ M.faceOf d ∉ faces := by
  rw [M.faceOf_facePerm]

/-- The outside face permutation is the face rotation restricted to the darts
based outside the region. -/
theorem outsideFacePerm_eq_subtypePerm (M : CombMap.{v})
    (faces : Finset M.Face) :
    outsideFacePerm M faces =
      M.facePerm.subtypePerm (p := fun d : M.Dart => M.faceOf d ∉ faces)
        (faceOf_notMem_facePerm_iff M faces) := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rfl

/-! ## The orbits of the outside face permutation -/

private noncomputable def outsideOrbitToFace (M : CombMap.{v})
    (faces : Finset M.Face) :
    CombMap.Orbit (outsideFacePerm M faces) → {f : M.Face // f ∉ faces} := by
  refine Quotient.lift
    (fun d : OutsideDart M faces =>
      (⟨M.faceOf d.1, d.2⟩ : {f : M.Face // f ∉ faces})) ?_
  intro x y hxy
  apply Subtype.ext
  have hsame : Equiv.Perm.SameCycle (outsideFacePerm M faces) x y := hxy
  rw [outsideFacePerm_eq_subtypePerm] at hsame
  have hval : Equiv.Perm.SameCycle M.facePerm x.1 y.1 :=
    (sameCycle_subtypePerm M.facePerm (faceOf_notMem_facePerm_iff M faces)
      x y).1 hsame
  exact (M.faceOf_eq_iff x.1 y.1).2 hval

private theorem outsideOrbitToFace_injective (M : CombMap.{v})
    (faces : Finset M.Face) :
    Function.Injective (outsideOrbitToFace M faces) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y hxy
  apply Quotient.sound
  have hface : M.faceOf x.1 = M.faceOf y.1 :=
    congrArg (fun z : {f : M.Face // f ∉ faces} => z.1) hxy
  have hsame : Equiv.Perm.SameCycle M.facePerm x.1 y.1 :=
    (M.faceOf_eq_iff x.1 y.1).1 hface
  show Equiv.Perm.SameCycle (outsideFacePerm M faces) x y
  rw [outsideFacePerm_eq_subtypePerm]
  exact (sameCycle_subtypePerm M.facePerm (faceOf_notMem_facePerm_iff M faces)
    x y).2 hsame

private theorem outsideOrbitToFace_surjective (M : CombMap.{v})
    (faces : Finset M.Face) :
    Function.Surjective (outsideOrbitToFace M faces) := by
  intro p
  obtain ⟨f, hf⟩ := p
  revert hf
  refine Quotient.inductionOn f ?_
  intro d hd
  exact ⟨Quotient.mk'' ⟨d, hd⟩, rfl⟩

/-- The orbits of the outside face permutation are the old faces based outside
the region. -/
noncomputable def outsideOrbitEquiv (M : CombMap.{v}) (faces : Finset M.Face) :
    CombMap.Orbit (outsideFacePerm M faces) ≃ {f : M.Face // f ∉ faces} :=
  Equiv.ofBijective (outsideOrbitToFace M faces)
    ⟨outsideOrbitToFace_injective M faces,
      outsideOrbitToFace_surjective M faces⟩

/-- The outside orbit of a dart is its old face. -/
theorem outsideOrbitEquiv_mk (M : CombMap.{v}) (faces : Finset M.Face)
    (d : OutsideDart M faces) :
    outsideOrbitEquiv M faces (Quotient.mk'' d) = ⟨M.faceOf d.1, d.2⟩ :=
  rfl

/-! ## The boundary cycle is a single orbit -/

/-- Any two positions lie in one cycle of the rotation of `Fin n`. -/
theorem sameCycle_finRotate (n : ℕ) (x y : Fin n) :
    Equiv.Perm.SameCycle (finRotate n) x y := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hxy : x = y := by
      apply Fin.eq_of_val_eq
      have hx := x.isLt
      have hy := y.isLt
      omega
    exact hxy.sameCycle (finRotate n)
  · have hcycle : Equiv.Perm.IsCycle (finRotate n) :=
      _root_.isCycle_finRotate_of_le hn
    have hsupp : (finRotate n).support = Finset.univ :=
      _root_.support_finRotate_of_le hn
    have hx : finRotate n x ≠ x := by
      have hmem : x ∈ (finRotate n).support := by
        rw [hsupp]
        exact Finset.mem_univ x
      exact Equiv.Perm.mem_support.mp hmem
    have hy : finRotate n y ≠ y := by
      have hmem : y ∈ (finRotate n).support := by
        rw [hsupp]
        exact Finset.mem_univ y
      exact Equiv.Perm.mem_support.mp hmem
    exact hcycle.sameCycle hx hy

/-- The boundary permutation is the rotation of positions transported along the
enumeration of the boundary cycle. -/
theorem boundaryPerm_eq_permCongr (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    boundary.boundaryPerm =
      boundary.positionEquiv.permCongr (finRotate boundary.cycle.length) := by
  apply Equiv.ext
  intro d
  rfl

/-- Any two oriented boundary darts lie in one cycle of the boundary
permutation. -/
theorem sameCycle_boundaryPerm (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (x y : BoundaryDart M faces) :
    Equiv.Perm.SameCycle boundary.boundaryPerm x y := by
  have hrot := sameCycle_finRotate boundary.cycle.length
    (boundary.positionEquiv.symm x) (boundary.positionEquiv.symm y)
  have htrans := (sameCycle_permCongr boundary.positionEquiv
    (finRotate boundary.cycle.length) (boundary.positionEquiv.symm x)
    (boundary.positionEquiv.symm y)).1 hrot
  rw [boundary.positionEquiv.apply_symm_apply x,
    boundary.positionEquiv.apply_symm_apply y] at htrans
  rw [boundaryPerm_eq_permCongr]
  exact htrans

/-- A boundary cycle has at least one oriented boundary dart. -/
theorem nonempty_boundaryDart (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) : Nonempty (BoundaryDart M faces) := by
  refine ⟨⟨boundary.cycle.head boundary.cycle_nonempty, ?_⟩⟩
  exact (boundary.cycle_mem_iff _).1 (List.head_mem boundary.cycle_nonempty)

/-- The boundary permutation has exactly one orbit, which is the new face. -/
noncomputable def boundaryOrbitEquivPUnit (M : CombMap.{v})
    (faces : Finset M.Face) (boundary : BoundaryCycle M faces) :
    CombMap.Orbit boundary.boundaryPerm ≃ PUnit.{v + 1} :=
  haveI : Nonempty (BoundaryDart M faces) := nonempty_boundaryDart M faces boundary
  orbitEquivPUnit boundary.boundaryPerm (sameCycle_boundaryPerm M faces boundary)

/-! ## The face permutation after reclosing -/

/-- The reclosed face permutation conjugates the sum of the outside rotation
and the boundary rotation by the split of the retained darts. -/
theorem reclosedFacePerm_eq_permCongr (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    reclosedFacePerm M faces boundary =
      (keptSplitEquiv M faces).symm.permCongr
        (Equiv.sumCongr (outsideFacePerm M faces) boundary.boundaryPerm) := by
  apply Equiv.ext
  intro d
  rfl

/-- The face permutation of the replaced map, in conjugated form. -/
theorem replaceGRegion_facePerm_eq (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    (replaceGRegion M faces region).facePerm =
      (keptSplitEquiv M faces).symm.permCongr
        (Equiv.sumCongr (outsideFacePerm M faces)
          region.toBoundaryCycle.boundaryPerm) := by
  have hface : (replaceGRegion M faces region).facePerm =
      reclosedFacePerm M faces region.toBoundaryCycle :=
    reclosedMap_facePerm M faces region.toBoundaryCycle
  exact hface.trans
    (reclosedFacePerm_eq_permCongr M faces region.toBoundaryCycle)

/-- Orbits transport along an equality of permutations. -/
def orbitCongrOfEq {α : Type v} {p q : Equiv.Perm α} (h : p = q) :
    CombMap.Orbit p ≃ CombMap.Orbit q :=
  Quotient.congr (Equiv.refl α) (fun a b => by
    constructor
    · intro hab
      have hp : Equiv.Perm.SameCycle p a b := hab
      rw [h] at hp
      exact hp
    · intro hab
      have hq : Equiv.Perm.SameCycle q a b := hab
      rw [← h] at hq
      exact hq)

/-! ## Splitting a retained dart -/

/-- A retained dart based inside the region is an oriented boundary dart. -/
theorem isBoundaryDart_of_mem (M : CombMap.{v}) (faces : Finset M.Face)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∈ faces) :
    IsBoundaryDart M faces d.1 := by
  refine ⟨hd, ?_⟩
  intro halpha
  exact d.property ⟨hd, halpha⟩

/-- The split sends a retained dart based outside the region to the left
summand. -/
theorem keptSplitEquiv_apply_of_notMem (M : CombMap.{v})
    (faces : Finset M.Face) (d : KeptDart M faces)
    (hd : M.faceOf d.1 ∉ faces) :
    keptSplitEquiv M faces d = Sum.inl ⟨d.1, hd⟩ := by
  refine (Equiv.apply_eq_iff_eq_symm_apply (keptSplitEquiv M faces)).2 ?_
  apply Subtype.ext
  rfl

/-- The split sends a retained dart based inside the region to the right
summand. -/
theorem keptSplitEquiv_apply_of_mem (M : CombMap.{v}) (faces : Finset M.Face)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∈ faces) :
    keptSplitEquiv M faces d =
      Sum.inr ⟨d.1, isBoundaryDart_of_mem M faces d hd⟩ := by
  refine (Equiv.apply_eq_iff_eq_symm_apply (keptSplitEquiv M faces)).2 ?_
  apply Subtype.ext
  rfl

/-! ## The faces of the replacement -/

/-- The faces of the replaced map are the old faces outside the region together
with the one new face. -/
noncomputable def replaceGRegionFaceEquiv (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces) :
    (replaceGRegion M faces region).Face ≃
      {f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1} :=
  (orbitCongrOfEq (replaceGRegion_facePerm_eq M faces region)).trans
    (((orbitPermCongr (keptSplitEquiv M faces).symm
          (Equiv.sumCongr (outsideFacePerm M faces)
            region.toBoundaryCycle.boundaryPerm)).symm).trans
      ((orbitSumCongr (outsideFacePerm M faces)
          region.toBoundaryCycle.boundaryPerm).trans
        (Equiv.sumCongr (outsideOrbitEquiv M faces)
          (boundaryOrbitEquivPUnit M faces region.toBoundaryCycle))))

/-- The face of a retained dart, before the split is evaluated. -/
theorem replaceGRegionFaceEquiv_faceOf (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (d : KeptDart M faces) :
    replaceGRegionFaceEquiv M faces region
        ((replaceGRegion M faces region).faceOf d) =
      Equiv.sumCongr (outsideOrbitEquiv M faces)
        (boundaryOrbitEquivPUnit M faces region.toBoundaryCycle)
        (orbitSumCongr (outsideFacePerm M faces)
          region.toBoundaryCycle.boundaryPerm
          (Quotient.mk'' (keptSplitEquiv M faces d))) :=
  rfl

/-- A retained dart based outside the region keeps its old face. -/
theorem replaceGRegionFaceEquiv_faceOf_notMem (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∉ faces) :
    replaceGRegionFaceEquiv M faces region
        ((replaceGRegion M faces region).faceOf d) =
      Sum.inl ⟨M.faceOf d.1, hd⟩ := by
  have hbase := replaceGRegionFaceEquiv_faceOf M faces region d
  rw [keptSplitEquiv_apply_of_notMem M faces d hd] at hbase
  exact hbase

/-- A retained dart based inside the region lands on the new face. -/
theorem replaceGRegionFaceEquiv_faceOf_mem (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (d : KeptDart M faces) (hd : M.faceOf d.1 ∈ faces) :
    replaceGRegionFaceEquiv M faces region
        ((replaceGRegion M faces region).faceOf d) =
      Sum.inr PUnit.unit := by
  have hbase := replaceGRegionFaceEquiv_faceOf M faces region d
  rw [keptSplitEquiv_apply_of_mem M faces d hd] at hbase
  exact hbase

/-! ## The face count of the replacement -/

/-- Replacing a region by one face leaves the number of faces outside the
region and adds one. -/
theorem replaceGRegion_faceCount (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    (replaceGRegion M faces region).faceCount + faces.card =
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
  have hnew : (replaceGRegion M faces region).faceCount =
      Nat.card {f : M.Face // f ∉ faces} + 1 := by
    have hcongr : Nat.card ((replaceGRegion M faces region).Face) =
        Nat.card ({f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1}) :=
      Nat.card_congr (replaceGRegionFaceEquiv M faces region)
    rw [Nat.card_sum, hunit] at hcongr
    exact hcongr
  rw [hnew, ← hmem, ← hcompl]
  omega

/-- Replacing a region of at least two faces strictly drops the face count. -/
theorem replaceGRegion_faceCount_lt (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (hcard : 2 ≤ faces.card) :
    (replaceGRegion M faces region).faceCount < M.faceCount := by
  have hcount := replaceGRegion_faceCount M faces region
  omega

/-- Replacing a single face leaves the face count unchanged. -/
theorem replaceGRegion_faceCount_of_card_eq_one (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (hcard : faces.card = 1) :
    (replaceGRegion M faces region).faceCount = M.faceCount := by
  have hcount := replaceGRegion_faceCount M faces region
  omega

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
