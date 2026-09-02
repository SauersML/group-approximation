import GroupApproximation.GGT.VanKampen.SurgeryFaceKept

/-!
# The boundary of the face created by a region collapse

`Surgery.MapCollapse.replaceGRegion` recloses the selected region along its
oriented boundary cycle.  This file shows that the retained darts of that cycle
are an ordered boundary of the new face, in the cycle's own order, so the word
of the new face is the word of the boundary cycle.

The rotation rule is the one proved in `SurgeryFaceKept`: on a dart based
inside the region the reclosed face rotation is the boundary rotation, which is
the position rotation of the enumeration transported by the position
equivalence.  The wrap-around of the enumeration comes from the two `finRotate`
value rules proved first.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe v

/-! ## Values of the position rotation -/

/-- Away from the last position the rotation of `Fin n` adds one. -/
theorem val_finRotate_of_lt {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (finRotate n i).val = i.val + 1 := by
  rcases n with _ | m
  · exact absurd i.isLt (Nat.not_lt_zero _)
  · have hne : i ≠ Fin.last m := by
      intro hlast
      rw [hlast, Fin.val_last] at hi
      omega
    exact coe_finRotate_of_ne_last hne

/-- At the last position the rotation of `Fin n` returns to zero. -/
theorem val_finRotate_of_eq {n : ℕ} (i : Fin n) (hi : i.val + 1 = n) :
    (finRotate n i).val = 0 := by
  rcases n with _ | m
  · exact absurd i.isLt (Nat.not_lt_zero _)
  · have hlast : i = Fin.last m := by
      apply Fin.eq_of_val_eq
      rw [Fin.val_last]
      omega
    rw [coe_finRotate, if_pos hlast]

/-! ## The position enumeration of the boundary cycle -/

/-- The position equivalence reads the boundary cycle at that position. -/
theorem positionEquiv_val (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (i : Fin boundary.cycle.length) :
    (boundary.positionEquiv i).1 = boundary.cycle.get i := rfl

/-- The boundary rotation advances the position by one. -/
theorem boundaryPerm_positionEquiv (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (i : Fin boundary.cycle.length) :
    boundary.boundaryPerm (boundary.positionEquiv i) =
      boundary.positionEquiv (finRotate boundary.cycle.length i) := by
  show boundary.positionEquiv (finRotate boundary.cycle.length
      (boundary.positionEquiv.symm (boundary.positionEquiv i))) =
    boundary.positionEquiv (finRotate boundary.cycle.length i)
  rw [Equiv.symm_apply_apply]

theorem boundaryPerm_positionEquiv_val (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (i : Fin boundary.cycle.length) :
    (boundary.boundaryPerm (boundary.positionEquiv i)).1 =
      boundary.cycle.get (finRotate boundary.cycle.length i) := by
  rw [boundaryPerm_positionEquiv]
  exact positionEquiv_val M faces boundary (finRotate boundary.cycle.length i)

/-- The boundary rotation of the dart at one position reads the cycle at the
rotated position. -/
theorem boundaryPerm_val_of_getElem (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (i : ℕ)
    (hi : i < boundary.cycle.length) (d : BoundaryDart M faces)
    (hd : d.1 = boundary.cycle[i]'hi) :
    (boundary.boundaryPerm d).1 =
      boundary.cycle.get (finRotate boundary.cycle.length ⟨i, hi⟩) := by
  have hpos : d = boundary.positionEquiv ⟨i, hi⟩ := by
    apply Subtype.ext
    rw [hd, positionEquiv_val, List.get_eq_getElem]
  rw [hpos]
  exact boundaryPerm_positionEquiv_val M faces boundary ⟨i, hi⟩

/-! ## The retained darts of the boundary cycle -/

/-- An oriented boundary dart is retained. -/
def keptDartOfIsBoundary (M : CombMap.{v}) (faces : Finset M.Face)
    (d : M.Dart) (hd : IsBoundaryDart M faces d) : KeptDart M faces := by
  refine ⟨d, ?_⟩
  intro hinternal
  exact hd.2 hinternal.2

theorem keptDartOfIsBoundary_val (M : CombMap.{v}) (faces : Finset M.Face)
    (d : M.Dart) (hd : IsBoundaryDart M faces d) :
    (keptDartOfIsBoundary M faces d hd).1 = d := rfl

theorem isBoundaryDart_of_mem_cycle (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (d : M.Dart)
    (hd : d ∈ boundary.cycle) : IsBoundaryDart M faces d :=
  (boundary.cycle_mem_iff d).1 hd

/-- The retained darts of the oriented boundary cycle, in the cycle's order. -/
def newFaceDarts (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) : List (KeptDart M faces) :=
  boundary.cycle.pmap (keptDartOfIsBoundary M faces)
    (isBoundaryDart_of_mem_cycle M faces boundary)

theorem newFaceDarts_ne_nil (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    newFaceDarts M faces boundary ≠ [] :=
  (List.pmap_ne_nil_iff (keptDartOfIsBoundary M faces)
    (isBoundaryDart_of_mem_cycle M faces boundary)).2 boundary.cycle_nonempty

theorem newFaceDarts_length (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    (newFaceDarts M faces boundary).length = boundary.cycle.length :=
  List.length_pmap

theorem newFaceDarts_getElem_val (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (i : ℕ)
    (hi : i < (newFaceDarts M faces boundary).length)
    (hj : i < boundary.cycle.length) :
    ((newFaceDarts M faces boundary)[i]'hi).1 = boundary.cycle[i]'hj :=
  congrArg (fun z : KeptDart M faces => z.1)
    (List.getElem_pmap (keptDartOfIsBoundary M faces)
      (isBoundaryDart_of_mem_cycle M faces boundary) hi)

theorem newFaceDarts_nodup (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    (newFaceDarts M faces boundary).Nodup := by
  refine List.Nodup.pmap ?_ boundary.cycle_nodup
  intro a ha b hb hab
  exact congrArg (fun z : KeptDart M faces => z.1) hab

theorem mem_newFaceDarts_iff (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (e : KeptDart M faces) :
    e ∈ newFaceDarts M faces region.toBoundaryCycle ↔
      (replaceGRegion M faces region).faceOf e = newFace M faces region := by
  constructor
  · intro hmem
    obtain ⟨a, ha, hae⟩ := List.mem_pmap.1 hmem
    have hb : IsBoundaryDart M faces a :=
      isBoundaryDart_of_mem_cycle M faces region.toBoundaryCycle a ha
    have hval : e.1 = a := by
      rw [← hae, keptDartOfIsBoundary_val]
    have hmemf : M.faceOf e.1 ∈ faces := by
      rw [hval]
      exact hb.1
    exact faceOf_eq_newFace M faces region e hmemf
  · intro hface
    have hmemf : M.faceOf e.1 ∈ faces :=
      faceOf_val_mem_of_eq_newFace M faces region e hface
    have hb : IsBoundaryDart M faces e.1 := isBoundaryDart_of_mem M faces e hmemf
    have hmemc : e.1 ∈ region.toBoundaryCycle.cycle :=
      (region.toBoundaryCycle.cycle_mem_iff e.1).2 hb
    refine List.mem_pmap.2 ⟨e.1, hmemc, ?_⟩
    apply Subtype.ext
    rfl

/-! ## Face rotation along the new boundary -/

/-- The reclosed face rotation reads the boundary cycle at the next
position. -/
theorem replaceGRegion_facePerm_newFaceDarts (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces) (i : ℕ)
    (hi : i < region.toBoundaryCycle.cycle.length)
    (hiv : i < (newFaceDarts M faces region.toBoundaryCycle).length) :
    ((replaceGRegion M faces region).facePerm
        ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv)).1 =
      region.toBoundaryCycle.cycle.get
        (finRotate region.toBoundaryCycle.cycle.length ⟨i, hi⟩) := by
  have hgetval : ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv).1 =
      region.toBoundaryCycle.cycle[i]'hi :=
    newFaceDarts_getElem_val M faces region.toBoundaryCycle i hiv hi
  have hmemf : M.faceOf
      ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv).1 ∈ faces := by
    rw [hgetval]
    exact (isBoundaryDart_of_mem_cycle M faces region.toBoundaryCycle _
      (List.getElem_mem hi)).1
  have hstep := replaceGRegion_facePerm_val_of_mem M faces region
    ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv) hmemf
  refine hstep.trans ?_
  exact boundaryPerm_val_of_getElem M faces region.toBoundaryCycle i hi
    ⟨((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv).1,
      isBoundaryDart_of_mem M faces
        ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv) hmemf⟩
    hgetval

theorem newFaceDarts_chain (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    (newFaceDarts M faces region.toBoundaryCycle).IsChain
      (fun x y => (replaceGRegion M faces region).facePerm x = y) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlen : (newFaceDarts M faces region.toBoundaryCycle).length =
      region.toBoundaryCycle.cycle.length :=
    newFaceDarts_length M faces region.toBoundaryCycle
  have hi1 : i + 1 < region.toBoundaryCycle.cycle.length := by
    rw [← hlen]
    exact hi
  have hi0 : i < region.toBoundaryCycle.cycle.length := by omega
  have hiv : i < (newFaceDarts M faces region.toBoundaryCycle).length := by omega
  have hrot : finRotate region.toBoundaryCycle.cycle.length ⟨i, hi0⟩ =
      ⟨i + 1, hi1⟩ :=
    Fin.eq_of_val_eq (val_finRotate_of_lt ⟨i, hi0⟩ hi1)
  apply Subtype.ext
  calc ((replaceGRegion M faces region).facePerm
          ((newFaceDarts M faces region.toBoundaryCycle)[i]'hiv)).1
      = region.toBoundaryCycle.cycle.get
          (finRotate region.toBoundaryCycle.cycle.length ⟨i, hi0⟩) :=
        replaceGRegion_facePerm_newFaceDarts M faces region i hi0 hiv
    _ = region.toBoundaryCycle.cycle.get ⟨i + 1, hi1⟩ :=
        congrArg (fun j => region.toBoundaryCycle.cycle.get j) hrot
    _ = ((newFaceDarts M faces region.toBoundaryCycle)[i + 1]'hi).1 :=
        (newFaceDarts_getElem_val M faces region.toBoundaryCycle (i + 1) hi
          hi1).symm

theorem newFaceDarts_closes (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    (replaceGRegion M faces region).facePerm
        ((newFaceDarts M faces region.toBoundaryCycle).getLast
          (newFaceDarts_ne_nil M faces region.toBoundaryCycle)) =
      (newFaceDarts M faces region.toBoundaryCycle).head
        (newFaceDarts_ne_nil M faces region.toBoundaryCycle) := by
  have hne := newFaceDarts_ne_nil M faces region.toBoundaryCycle
  have hlen : (newFaceDarts M faces region.toBoundaryCycle).length =
      region.toBoundaryCycle.cycle.length :=
    newFaceDarts_length M faces region.toBoundaryCycle
  have hm0 : 0 < region.toBoundaryCycle.cycle.length :=
    List.length_pos_iff.2 region.toBoundaryCycle.cycle_nonempty
  have hlv : (newFaceDarts M faces region.toBoundaryCycle).length - 1 <
      (newFaceDarts M faces region.toBoundaryCycle).length := by omega
  have hlc : (newFaceDarts M faces region.toBoundaryCycle).length - 1 <
      region.toBoundaryCycle.cycle.length := by omega
  have h0v : 0 < (newFaceDarts M faces region.toBoundaryCycle).length := by omega
  have hsucc : (newFaceDarts M faces region.toBoundaryCycle).length - 1 + 1 =
      region.toBoundaryCycle.cycle.length := by omega
  have hrot : finRotate region.toBoundaryCycle.cycle.length
      ⟨(newFaceDarts M faces region.toBoundaryCycle).length - 1, hlc⟩ =
      ⟨0, hm0⟩ :=
    Fin.eq_of_val_eq (val_finRotate_of_eq
      ⟨(newFaceDarts M faces region.toBoundaryCycle).length - 1, hlc⟩ hsucc)
  apply Subtype.ext
  calc ((replaceGRegion M faces region).facePerm
          ((newFaceDarts M faces region.toBoundaryCycle).getLast hne)).1
      = ((replaceGRegion M faces region).facePerm
          ((newFaceDarts M faces region.toBoundaryCycle)[
            (newFaceDarts M faces region.toBoundaryCycle).length - 1]'hlv)).1 :=
        congrArg (fun z : KeptDart M faces =>
            ((replaceGRegion M faces region).facePerm z).1)
          (List.getLast_eq_getElem hne)
    _ = region.toBoundaryCycle.cycle.get
          (finRotate region.toBoundaryCycle.cycle.length
            ⟨(newFaceDarts M faces region.toBoundaryCycle).length - 1, hlc⟩) :=
        replaceGRegion_facePerm_newFaceDarts M faces region _ hlc hlv
    _ = region.toBoundaryCycle.cycle.get ⟨0, hm0⟩ :=
        congrArg (fun j => region.toBoundaryCycle.cycle.get j) hrot
    _ = ((newFaceDarts M faces region.toBoundaryCycle)[0]'h0v).1 :=
        (newFaceDarts_getElem_val M faces region.toBoundaryCycle 0 h0v hm0).symm
    _ = ((newFaceDarts M faces region.toBoundaryCycle).head hne).1 :=
        congrArg (fun z : KeptDart M faces => z.1)
          (List.head_eq_getElem hne).symm

/-- The ordered boundary of the face created by the collapse. -/
noncomputable def newFaceBoundary (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    FaceBoundary (replaceGRegion M faces region) (newFace M faces region) where
  darts := newFaceDarts M faces region.toBoundaryCycle
  nonempty := newFaceDarts_ne_nil M faces region.toBoundaryCycle
  nodup := newFaceDarts_nodup M faces region.toBoundaryCycle
  mem_iff := fun e => mem_newFaceDarts_iff M faces region e
  chain := newFaceDarts_chain M faces region
  closes := newFaceDarts_closes M faces region
  length_eq_degree :=
    length_eq_faceDegree_of_nodup (replaceGRegion M faces region)
      (newFace M faces region) (newFaceDarts M faces region.toBoundaryCycle)
      (newFaceDarts_nodup M faces region.toBoundaryCycle)
      (fun e => mem_newFaceDarts_iff M faces region e)

/-- Forgetting the retained-dart proofs returns the oriented boundary cycle, so
the new face has the boundary cycle's word. -/
theorem newFaceBoundary_darts_map_val (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) :
    (newFaceBoundary M faces region).darts.map Subtype.val =
      region.toBoundaryCycle.cycle := by
  show (region.toBoundaryCycle.cycle.pmap (keptDartOfIsBoundary M faces)
      (isBoundaryDart_of_mem_cycle M faces region.toBoundaryCycle)).map
      Subtype.val = region.toBoundaryCycle.cycle
  rw [List.map_pmap, List.pmap_eq_self]
  intro a h
  rfl

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
