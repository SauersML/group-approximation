import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassBasic
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket class avoids the two cells, no bridge

Lane `gl-p07-03` of the route 3 cartography (`lanes/carto-gl-p07.md`), second module.  This is
infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, from Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  It certifies no printed sentence on its own.

## Proof route

1. `cell_face_not_mem_sideFaces`: take a cell arc `A` of `Π_k` with `0 < |A|` whose reverse
   `invDarts A` lies on a noncrossing closed walk `L`.  Pick `e ∈ A`.  Then `α e ∈ L`, so `α e` is
   a boundary dart of `sideFaces L` (`isBoundaryDart_sideFaces_iff`).  Hence
   `faceOf (α α e) = faceOf e = Π_k ∉ sideFaces L`.
2. `pocketClass_ne_cell_left` and `pocketClass_ne_cell_right`: the class lies in `sideFaces K.walk`
   (`mem_sideFaces_of_mem_pocketClass`), and step 1 applies to `K.firstArc` and `K.secondArc`.
3. `pocketClass_noBridge`: let `d` be a kept dart with both sides in the class.
   * If `d` or `α d` lies on `K.walk`, one side is off `sideFaces K.walk`.
   * If `d` or `α d` lies on `∂a`, one side is in `a`, but the class avoids `a`.
   * The same holds for `∂b`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

namespace PocketClass

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

theorem mem_walk_of_mem_invDarts_firstArc (K : CellPocketWalk D eps X i j)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.firstArc.darts) : d ∈ K.walk := by
  show d ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
    invDarts X K.secondArc.darts
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.mem_walk_of_mem_invDarts_firstArc

theorem mem_walk_of_mem_invDarts_secondArc (K : CellPocketWalk D eps X i j)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.secondArc.darts) : d ∈ K.walk := by
  show d ∈ K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
    invDarts X K.secondArc.darts
  exact List.mem_append_right _ hd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.mem_walk_of_mem_invDarts_secondArc

/-- A cell whose nonempty arc, read backwards, lies on a noncrossing closed walk is off the side
of that walk. -/
theorem cell_face_not_mem_sideFaces {L : List X.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk X.toCombMap L) {k : Fin X.rCellCount}
    (A : CyclicArc (cellDarts X k)) (hpos : 0 < A.length)
    (hsub : ∀ d ∈ invDarts X A.darts, d ∈ L) :
    (cell X k).face ∉ sideFaces X.toCombMap L := by
  have hlen : 0 < A.darts.length := by
    rw [A.darts_length]
    exact hpos
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hlen
  have hinv : X.toCombMap.alpha e ∈ invDarts X A.darts := by
    show X.toCombMap.alpha e ∈ A.darts.reverse.map X.toCombMap.alpha
    exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩
  have hb : X.toCombMap.faceOf (X.toCombMap.alpha e) ∈ sideFaces X.toCombMap L ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha e)) ∉
        sideFaces X.toCombMap L :=
    (hw.isBoundaryDart_sideFaces_iff X.planar (X.toCombMap.alpha e)).mpr (hsub _ hinv)
  have hface : X.toCombMap.faceOf e = (cell X k).face :=
    ((X.faceBoundary (cell X k).face).mem_iff e).mp (A.mem_cycle_of_mem_darts he)
  have hout := hb.2
  rw [X.toCombMap.alpha_involutive e, hface] at hout
  exact hout

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.cell_face_not_mem_sideFaces

/-- The class of a side face of `K.walk` misses the cell `Π_i`. -/
theorem pocketClass_ne_cell_left {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    {c f : X.toCombMap.Face} (hc : c ∈ sideFaces X.toCombMap K.walk)
    (hf : f ∈ pocketClass a b K c) : f ≠ (cell X i).face := by
  intro h
  have hs := mem_sideFaces_of_mem_pocketClass hc hf
  rw [h] at hs
  exact cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
    (fun _ hd => mem_walk_of_mem_invDarts_firstArc K hd) hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketClass_ne_cell_left

/-- The class of a side face of `K.walk` misses the cell `Π_j`. -/
theorem pocketClass_ne_cell_right {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    {c f : X.toCombMap.Face} (hc : c ∈ sideFaces X.toCombMap K.walk)
    (hf : f ∈ pocketClass a b K c) : f ≠ (cell X j).face := by
  intro h
  have hs := mem_sideFaces_of_mem_pocketClass hc hf
  rw [h] at hs
  exact cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos
    (fun _ hd => mem_walk_of_mem_invDarts_secondArc K hd) hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketClass_ne_cell_right

/-- **No bridge.**  A kept edge never has both sides in the class of a side face of `K.walk` that
lies outside both regions. -/
theorem pocketClass_noBridge {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    {c : X.toCombMap.Face} (hc : c ∈ sideFaces X.toCombMap K.walk) (hca : c ∉ a.1)
    (hcb : c ∉ b.1) (d : X.toCombMap.Dart) (hd : pocketKeep a b K d) :
    ¬ (X.toCombMap.faceOf d ∈ pocketClass a b K c ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ pocketClass a b K c) := by
  rintro ⟨h₁, h₂⟩
  rcases hd with hKd | hAd | hBd
  · rcases hKd with hdK | haK
    · have hB : X.toCombMap.faceOf d ∈ sideFaces X.toCombMap K.walk ∧
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ sideFaces X.toCombMap K.walk :=
        (hw.isBoundaryDart_sideFaces_iff X.planar d).mpr hdK
      exact hB.2 (mem_sideFaces_of_mem_pocketClass hc h₂)
    · have hB : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
          X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉
            sideFaces X.toCombMap K.walk :=
        (hw.isBoundaryDart_sideFaces_iff X.planar (X.toCombMap.alpha d)).mpr haK
      have hout := hB.2
      rw [X.toCombMap.alpha_involutive d] at hout
      exact hout (mem_sideFaces_of_mem_pocketClass hc h₁)
  · rcases hAd with hda | hada
    · have hB : X.toCombMap.faceOf d ∈ a.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 :=
        (a.2.boundary.cycle_mem_iff d).mp hda
      exact not_mem_left_of_mem_pocketClass hca h₁ hB.1
    · have hB : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ a.1 ∧
          X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉ a.1 :=
        (a.2.boundary.cycle_mem_iff (X.toCombMap.alpha d)).mp hada
      exact not_mem_left_of_mem_pocketClass hca h₂ hB.1
  · rcases hBd with hdb | hadb
    · have hB : X.toCombMap.faceOf d ∈ b.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 :=
        (b.2.boundary.cycle_mem_iff d).mp hdb
      exact not_mem_right_of_mem_pocketClass hcb h₁ hB.1
    · have hB : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ b.1 ∧
          X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) ∉ b.1 :=
        (b.2.boundary.cycle_mem_iff (X.toCombMap.alpha d)).mp hadb
      exact not_mem_right_of_mem_pocketClass hcb h₂ hB.1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketClass_noBridge

end PocketClass

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
