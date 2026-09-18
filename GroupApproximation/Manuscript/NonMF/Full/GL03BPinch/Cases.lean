import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.LakeArc
import GroupApproximation.Meta.AxiomGuard

/-!
# The corrected enclosed inner pocket: the lake-filling cases

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `K = s₁ t₁⁻¹ s₂ t₂⁻¹` be the pocket walk and let `Cmp` be the exterior piece, the component of
the outer face off the side faces of `K`.  Fill every other face, giving the face set `F = absorbed`.
It is an enclosed face set turning to successors over the outer walk `lakeWalk` from any walk-facing
dart on `Cmp` (`LakeFill.lakeWalk_enclosedFaceSetSucc`).  A relator cell `C` on the side of `K` is
off `Cmp`, so it lies in `F`.

`TwoArcConclusion eps X` is the conclusion of `InnerPocketEnclosedTwoArcCorrected`, word for word.
* `twoArcConclusion_of_lakes`: neither `Π_i` nor `Π_j` is in `Cmp`.  The outer walk reverses side
  darts only, so it has at most `2ε` darts.  If some cell `Π_k` is off `F`, take `k₁ = k₂ = k` with
  empty arcs.  Otherwise every relator cell is in `F`, which is the second disjunct.
* `twoArcConclusion_of_firstExterior`: only `Π_i` is in `Cmp`.  Start the outer walk at the first
  dart of `t₁`.  It reads `t₁`, then at most `|s₁| + |s₂| ≤ 2ε` darts reversing side darts.
  Take `k₁ = k₂ = i`, `A₁` empty and `A₂ = t₁`.
* `twoArcConclusion_of_secondExterior`: symmetric, with `t₂`.
* `twoArcConclusion_of_ordered`: both cells are in `Cmp`, and the outer walk reads
  `s₁' t₁⁻¹ s₂' t₂⁻¹` in order with short sides.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex 2134); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.Full.GL03BPinch

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The conclusion of the corrected enclosed inner pocket** (`thm:hull`), word for word the
conclusion of `InnerPocketEnclosedTwoArcCorrected`. -/
def TwoArcConclusion (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
    (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
    (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X faces outerWalk ∧
      (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
      (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
      Embedded.invDarts X outerWalk =
        s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)) ∨
  ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X faces outerWalk ∧
      (∀ C' ∈ X.relatorCells, C'.face ∈ faces) ∧ outerWalk.length ≤ eps + eps

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The inverse of the empty dart list is empty (`thm:hull`). -/
theorem pinch_invDarts_nil : invDarts X ([] : List X.toCombMap.Dart) = [] :=
  rfl

/-- A face on the side of a walk is absorbed (`thm:hull`). -/
theorem mem_absorbed_of_mem_sideFaces {wk : List X.toCombMap.Dart}
    (hout : X.outerFace ∉ sideFaces X.toCombMap wk) {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap wk) :
    f ∈ absorbed X.toCombMap (sideFaces X.toCombMap wk) X.outerFace :=
  mem_absorbed_iff.mpr (not_mem_component_of_mem_sideFaces hout hf)

/-- **Lake filling when both cells are lakes** (`thm:hull`). -/
theorem twoArcConclusion_of_lakes (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ sideFaces X.toCombMap K.walk) :
    TwoArcConclusion eps X := by
  obtain ⟨x₀, hx₀⟩ := exists_start K hw hout
  have hlen := lakeWalk_length_le_of_lakes K hw hout hi hj hx₀
  by_cases hoff : ∃ k : Fin X.rCellCount,
      (cell X k).face ∉ absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace
  · obtain ⟨k, hk⟩ := hoff
    obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two hlen
    refine Or.inl ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
      lakeWalk X.toCombMap K.walk x₀, k, k, emptyArc (cellDarts X k), emptyArc (cellDarts X k),
      s₁, s₂, lakeWalk_enclosedFaceSetSucc X hw hout hx₀,
      ⟨C, hC, mem_absorbed_of_mem_sideFaces hout hCf⟩, hk, hk, ?_, hs₁, hs₂, Or.inl rfl⟩
    rw [emptyArc_darts, pinch_invDarts_nil]
    simp only [List.append_nil]
    exact hsplit
  · refine Or.inr ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
      lakeWalk X.toCombMap K.walk x₀, lakeWalk_enclosedFaceSetSucc X hw hout hx₀, ?_, ?_⟩
    · intro C' hC'
      obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hC'
      by_contra hk
      exact hoff ⟨⟨n, hn⟩, hk⟩
    · simp only [invDarts, List.length_map, List.length_reverse] at hlen
      exact hlen

/-- **Lake filling when only `Π_i` is exterior** (`thm:hull`). -/
theorem twoArcConclusion_of_firstExterior (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ sideFaces X.toCombMap K.walk) :
    TwoArcConclusion eps X := by
  obtain ⟨x₀, R, hx₀, hL, hR⟩ := exists_lakeWalk_arc (s := K.firstSide ++ K.secondSide) hw hout
    K.firstArc K.firstArc_pos (fun _ hx => alpha_mem_walk_firstArc K hx) hi
    fun _ hα hc hrA => alpha_mem_sides K hα hrA (not_mem_arc_of_faceOf K.secondArc hc hj)
  obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two (invDarts_length_le_sides K hR)
  refine Or.inl ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, i, i, emptyArc (cellDarts X i), K.firstArc, s₁, s₂,
    lakeWalk_enclosedFaceSetSucc X hw hout hx₀, ⟨C, hC, mem_absorbed_of_mem_sideFaces hout hCf⟩,
    fun h => mem_absorbed_iff.mp h hi, fun h => mem_absorbed_iff.mp h hi, ?_, hs₁, hs₂,
    Or.inr K.firstArc_pos⟩
  rw [emptyArc_darts, pinch_invDarts_nil, List.append_nil, hL, pinch_invDarts_append, hsplit]

/-- **Lake filling when only `Π_j` is exterior** (`thm:hull`). -/
theorem twoArcConclusion_of_secondExterior (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∉ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ sideFaces X.toCombMap K.walk) :
    TwoArcConclusion eps X := by
  obtain ⟨x₀, R, hx₀, hL, hR⟩ := exists_lakeWalk_arc (s := K.firstSide ++ K.secondSide) hw hout
    K.secondArc K.secondArc_pos (fun _ hx => alpha_mem_walk_secondArc K hx) hj
    fun _ hα hc hrA => alpha_mem_sides K hα (not_mem_arc_of_faceOf K.firstArc hc hi) hrA
  obtain ⟨s₁, s₂, hs₁, hs₂, hsplit⟩ := exists_split_two (invDarts_length_le_sides K hR)
  refine Or.inl ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, j, j, emptyArc (cellDarts X j), K.secondArc, s₁, s₂,
    lakeWalk_enclosedFaceSetSucc X hw hout hx₀, ⟨C, hC, mem_absorbed_of_mem_sideFaces hout hCf⟩,
    fun h => mem_absorbed_iff.mp h hj, fun h => mem_absorbed_iff.mp h hj, ?_, hs₁, hs₂,
    Or.inr K.secondArc_pos⟩
  rw [emptyArc_darts, pinch_invDarts_nil, List.append_nil, hL, pinch_invDarts_append, hsplit]

/-- **Lake filling when both cells are exterior** (`thm:hull`).  Given an outer walk from a dart on
the exterior piece that reads `s₁' t₁⁻¹ s₂' t₂⁻¹` in order with `|s₁'|, |s₂'| ≤ ε`, the filled face
set gives the first disjunct with `k₁ = i` and `k₂ = j`. -/
theorem twoArcConclusion_of_ordered (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hi : (cell X i).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (hj : (cell X j).face ∈ component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    {x₀ : (walkMap X.toCombMap K.walk).Dart} {s₁ s₂ : List X.toCombMap.Dart}
    (hx₀ : X.toCombMap.faceOf x₀.1 ∈
      component X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace)
    (heq : invDarts X (lakeWalk X.toCombMap K.walk x₀) =
      s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ sideFaces X.toCombMap K.walk) :
    TwoArcConclusion eps X :=
  Or.inl ⟨absorbed X.toCombMap (sideFaces X.toCombMap K.walk) X.outerFace,
    lakeWalk X.toCombMap K.walk x₀, i, j, K.firstArc, K.secondArc, s₁, s₂,
    lakeWalk_enclosedFaceSetSucc X hw hout hx₀, ⟨C, hC, mem_absorbed_of_mem_sideFaces hout hCf⟩,
    fun h => mem_absorbed_iff.mp h hi, fun h => mem_absorbed_iff.mp h hj, heq, hs₁, hs₂,
    Or.inr K.secondArc_pos⟩

end GroupApproximation.Full.GL03BPinch

#audit_axioms GroupApproximation.Full.GL03BPinch.pinch_invDarts_nil
#audit_axioms GroupApproximation.Full.GL03BPinch.mem_absorbed_of_mem_sideFaces
#audit_axioms GroupApproximation.Full.GL03BPinch.twoArcConclusion_of_lakes
#audit_axioms GroupApproximation.Full.GL03BPinch.twoArcConclusion_of_firstExterior
#audit_axioms GroupApproximation.Full.GL03BPinch.twoArcConclusion_of_secondExterior
#audit_axioms GroupApproximation.Full.GL03BPinch.twoArcConclusion_of_ordered
