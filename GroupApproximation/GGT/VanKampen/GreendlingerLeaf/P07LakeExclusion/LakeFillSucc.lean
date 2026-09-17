import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lake filling: the endpoint `lakeFillSucc`

Proof of `LakeFillSuccStatement` (`GreendlingerLeaf/P07LakeExclusion/Proof.lean`).  Write `w` for
the pocket walk `s₁ t₁⁻¹ s₂ t₂⁻¹`, `C` for the exterior piece (the component of the outer face in the
complement of the side faces of `w`) and `F = absorbed` for its complement (every lake filled).  The
outer walk of `F` is `lakeWalk w x₀` for any walk-facing dart `x₀` on a face of `C`
(`lakeWalk_enclosedFaceSetSucc`); its darts are exactly the darts on faces of `C` whose reverses lie
on `w` (`mem_lakeWalk_iff`).

* A full arc makes its cell a lake (`firstFace_not_mem_component`), so that relator cell is in `F`.
* **`Π_j` in `C` (the first arc full).**  Start the outer walk at the first dart of `t₂`: it reads
  `t₂` and then darts on faces of `C` reversing no arc dart of `t₁` (whose cell is a lake) nor of
  `t₂` (already read), hence reversing side darts, at most `|s₁| + |s₂| ≤ 2ε` of them.  Splitting
  their inverse in two gives `s₁'`, `s₂'`, and the inverse outer walk reads `s₁' s₂' t₂⁻¹` with
  `Π_j` off `F`.
* **`Π_i` in `C` (the second arc full).**  Symmetric, with `t₁`.
* **Both cells lakes.**  Every outer walk dart reverses a side dart, so the inverse outer walk is
  `s₁' s₂'`; then either some relator cell is off `F` (take its empty arc) or all are in `F`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

section Cases

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Lake filling when `Π_j` is exterior** (the first arc is full). -/
theorem lakeFill_secondExterior (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hfull : K.firstArc.length = (cellDarts X i).length)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
      (s₁ s₂ : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk ∧
        (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
        ((∃ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
            (cell X k).face ∉ faces ∧ invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts) ∨
          ((∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) ∧
            invDarts X outerWalk = s₁ ++ s₂)) := by
  have hi := firstFace_not_mem_component K hw hfull
  obtain ⟨x₀, R, hx₀, hL, hR⟩ := exists_lakeWalk_arc (s := K.firstSide ++ K.secondSide) hw hout
    K.secondArc K.secondArc_pos (fun _ hx => alpha_mem_walk_secondArc K hx) hj
    fun _ hα hc hrA => alpha_mem_sides K hα (not_mem_arc_of_faceOf K.firstArc hc hi) hrA
  obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two (invDarts_length_le_sides K hR)
  refine ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, s₁, s₂, lakeWalk_enclosedFaceSetSucc X hw hout hx₀,
    ⟨cell X i, cell_mem X i, mem_absorbed_iff.mpr hi⟩, hs₁, hs₂,
    Or.inl ⟨j, K.secondArc, fun h => mem_absorbed_iff.mp h hj, ?_⟩⟩
  rw [hL, lakeFill_invDarts_append, hsplit]

/-- **Lake filling when `Π_i` is exterior** (the second arc is full). -/
theorem lakeFill_firstExterior (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hfull : K.secondArc.length = (cellDarts X j).length)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
      (s₁ s₂ : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk ∧
        (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
        ((∃ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
            (cell X k).face ∉ faces ∧ invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts) ∨
          ((∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) ∧
            invDarts X outerWalk = s₁ ++ s₂)) := by
  have hj := secondFace_not_mem_component K hw hfull
  obtain ⟨x₀, R, hx₀, hL, hR⟩ := exists_lakeWalk_arc (s := K.firstSide ++ K.secondSide) hw hout
    K.firstArc K.firstArc_pos (fun _ hx => alpha_mem_walk_firstArc K hx) hi
    fun _ hα hc hrA => alpha_mem_sides K hα hrA (not_mem_arc_of_faceOf K.secondArc hc hj)
  obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two (invDarts_length_le_sides K hR)
  refine ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, s₁, s₂, lakeWalk_enclosedFaceSetSucc X hw hout hx₀,
    ⟨cell X j, cell_mem X j, mem_absorbed_iff.mpr hj⟩, hs₁, hs₂,
    Or.inl ⟨i, K.firstArc, fun h => mem_absorbed_iff.mp h hi, ?_⟩⟩
  rw [hL, lakeFill_invDarts_append, hsplit]

/-- **Lake filling when both cells are lakes.** -/
theorem lakeFill_bothLakes (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace) :
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
      (s₁ s₂ : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk ∧
        (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
        ((∃ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
            (cell X k).face ∉ faces ∧ invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts) ∨
          ((∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) ∧
            invDarts X outerWalk = s₁ ++ s₂)) := by
  obtain ⟨d, hα, hc⟩ := exists_alpha_mem_component hw X.planar hout
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (walkMap X.toCombMap K.walk).Dart, X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace :=
    ⟨⟨d, Or.inr hα⟩, hc⟩
  have hsides : ∀ r ∈ lakeWalk X.toCombMap K.walk x₀,
      X.toCombMap.alpha r ∈ K.firstSide ++ K.secondSide := by
    intro r hr
    obtain ⟨hα', hc'⟩ := (mem_lakeWalk_iff hw X.planar hout hx₀ r).mp hr
    exact alpha_mem_sides K hα' (not_mem_arc_of_faceOf K.firstArc hc' hi)
      (not_mem_arc_of_faceOf K.secondArc hc' hj)
  obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two
    (invDarts_length_le_sides K (length_le_of_forall_alpha_mem (lakeWalk_nodup x₀) hsides))
  refine ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, s₁, s₂, lakeWalk_enclosedFaceSetSucc X hw hout hx₀,
    ⟨cell X i, cell_mem X i, mem_absorbed_iff.mpr hi⟩, hs₁, hs₂, ?_⟩
  by_cases hoff : ∃ k : Fin X.rCellCount,
      (cell X k).face ∉ absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
  · obtain ⟨k, hk⟩ := hoff
    refine Or.inl ⟨k, emptyArc (cellDarts X k), hk, ?_⟩
    rw [hsplit, invDarts_emptyArc, List.append_nil]
  · refine Or.inr ⟨fun k => ?_, hsplit⟩
    by_contra hk
    exact hoff ⟨k, hk⟩

end Cases

/-- **Step 1 of the lake exclusion: filling the lakes of a pocket walk with a full arc.** -/
theorem lakeFillSucc : LakeFillSuccStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K _ hw hout hfull
  by_cases hj : (cell X j).face ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
  · exact lakeFill_secondExterior K hw hout
      (hfull.resolve_right fun h => secondFace_not_mem_component K hw h hj) hj
  · by_cases hi : (cell X i).face ∈
        component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
    · exact lakeFill_firstExterior K hw hout
        (hfull.resolve_left fun h => firstFace_not_mem_component K hw h hi) hi
    · exact lakeFill_bothLakes K hw hout hi hj

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeFill_secondExterior
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeFill_firstExterior
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeFill_bothLakes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill.lakeFillSucc
